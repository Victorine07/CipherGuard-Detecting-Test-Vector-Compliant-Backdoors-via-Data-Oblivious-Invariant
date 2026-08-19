#!/usr/bin/env python3
"""e13_adaptive_evasion.py -- adaptive-adversary stress test beyond S7/S8.

An attacker who has read the paper knows the interprocedural check looks for (a) a secret-dependent
branch and (b) a key-tainted value in a bare arithmetic op, and that it treats key-schedule-named
functions as sanitizers. We construct two evasions that target exactly these mechanisms, and we test
them honestly against the current check and against a hardened check:

  A1  sanitizer abuse : launder the raw key through a fake helper whose NAME looks like a key
                        schedule (an identity `def ..._key_expand(k): return k`), so the name-based
                        sanitizer heuristic treats the leaked value as a legitimately derived key.
  A3  subscript leak  : leak the key through a list index (`return sel[flag]`) rather than an
                        arithmetic op, side-stepping the dataflow test's BinOp-only check.

Both are validated as real backdoors (pass the test vector, exploitable). We report which evade the
current check, then harden the check (structural sanitizer + output-taint dataflow) and re-test,
including a regression check that the six/eight benchmark styles stay caught and clean FPR stays 0.

"""
from __future__ import annotations
import ast
import random
import sys
import time
from datetime import datetime
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))

from src.common.logging import get_logger
from src.common.io import read_json, write_json
from src.common.paths import MODELS_DIR, REGISTRY, REPORTS, ensure
from src.tamper.backdoor_styles import _enc_pk, exploit_S5, Style, validate_style, STYLES
from src.models.interproc import cipherguard_interproc
from src.models.ct_baseline import ct_control_flow_violation

AEAD = ("ascon", "gift_cofb")


# --- adaptive injectors (block==key ciphers so the full-key leak equals secret & mask) --------
def inject_A1(source, ctx, rng):
    """Sanitizer abuse: raw key laundered through a fake key-schedule-named identity helper."""
    tree = ast.parse(source); stem = ctx["stem"]; block = ctx["block_size"]
    fd, p, k = _enc_pk(tree, stem)
    if fd is None:
        return None, {"reason": "no encrypt"}
    ridx = max((i for i, s in enumerate(fd.body) if isinstance(s, ast.Return)), default=None)
    if ridx is None:
        return None, {"reason": "no return"}
    t = min(16, block); mask, bm = (1 << t) - 1, (1 << block) - 1; trig = 0x1337 & mask
    hn = f"{stem}_key_expand_helper"          # 'expand' -> matched by the sanitizer heuristic
    helper = f"def {hn}(k):\n    return k\n"   # identity: launders the master key
    repl = ast.parse(
        f"__cg_ct = 0\n"
        f"__cg_lk = {hn}({k})\n"
        f"__cg_flag = int(({p} & {hex(mask)}) == {hex(trig)})\n"
        f"__cg_ct = __cg_ct * (1 - __cg_flag) | ((__cg_lk & {hex(bm)}) * __cg_flag)\n"
        f"return __cg_ct\n").body
    repl[0].value = fd.body[ridx].value
    fd.body[ridx:ridx + 1] = repl
    tree.body.append(ast.parse(helper).body[0])
    ast.fix_missing_locations(tree)
    return ast.unparse(tree), {"style": "A1", "t": t, "trigger_val": trig, "helper": hn}


def inject_A3(source, ctx, rng):
    """Subscript leak: leak via list indexing instead of arithmetic (evades the BinOp-only test)."""
    tree = ast.parse(source); stem = ctx["stem"]; block = ctx["block_size"]
    fd, p, k = _enc_pk(tree, stem)
    if fd is None:
        return None, {"reason": "no encrypt"}
    ridx = max((i for i, s in enumerate(fd.body) if isinstance(s, ast.Return)), default=None)
    if ridx is None:
        return None, {"reason": "no return"}
    t = min(16, block); mask = (1 << t) - 1; trig = 0x1337 & mask
    repl = ast.parse(
        f"__cg_ct = 0\n"
        f"__cg_sel = [__cg_ct, {k}]\n"                # list holds the raw key; no BinOp
        f"__cg_flag = int(({p} & {hex(mask)}) == {hex(trig)})\n"
        f"return __cg_sel[__cg_flag]\n").body          # leak via subscript, not arithmetic
    repl[0].value = fd.body[ridx].value
    fd.body[ridx:ridx + 1] = repl
    ast.fix_missing_locations(tree)
    return ast.unparse(tree), {"style": "A3", "t": t, "trigger_val": trig}


ADAPTIVE = {
    "A1": Style("A1", "sanitizer abuse (fake key-schedule launder)", inject_A1, exploit_S5),
    "A3": Style("A3", "subscript leak (evades BinOp-only dataflow)", inject_A3, exploit_S5),
}


def cg(src, stem, ks, harden):
    return cipherguard_interproc(src, stem, ks, harden=harden)


def main() -> int:
    log = get_logger("e13_adaptive_evasion")
    t0 = time.time()
    reg = {read_json(p)["variant"].lower(): read_json(p) for p in REGISTRY.glob("*.json")}
    aead = ("ascon", "gift_cofb")
    blocks = [s for s in reg if not any(s.startswith(a) for a in aead)]
    bases = [s for s in ("speck_128_128", "simon_128_128", "cham_128_128") if s in reg]

    # --- Part 1: adaptive evasions before/after hardening ---------------------------------------
    log.ckpt("adaptive A1/A3: construct, validate, test naive vs hardened check", 1, 3)
    rows = []
    for stem in bases:
        e = reg[stem]; block, key = e["block_size"], e["key_size"]
        ks = (e.get("tamperable_sites", {}) or {}).get("key_schedule", []) or []
        ctx = {"stem": stem, "block_size": block, "key_size": key, "keysched_names": ks}
        clean_src = (MODELS_DIR / f"{stem}.py").read_text()
        for aid, style in ADAPTIVE.items():
            tsrc, meta = style.inject(clean_src, ctx, random.Random(7))
            if tsrc is None:
                log.warn(f"{stem}/{aid}: inject failed ({meta.get('reason')})"); continue
            ok, _ = validate_style(clean_src, tsrc, stem, block, key, style, meta)
            if not ok:
                log.warn(f"{stem}/{aid}: not a valid backdoor; skipping"); continue
            naive = cg(tsrc, stem, ks, harden=False)
            hard = cg(tsrc, stem, ks, harden=True)
            cta = ct_control_flow_violation(tsrc, stem)
            rows.append({"base": stem, "id": aid, "valid_backdoor": True,
                         "naive_check": naive, "hardened_check": hard, "ct_analyzer": cta})
            log.info(f"  {stem}/{aid}: valid; naive {'CAUGHT' if naive else 'EVADED'} -> "
                     f"hardened {'CAUGHT' if hard else 'EVADED'} (CT analyzer {'CAUGHT' if cta else 'EVADED'})")

    # --- Part 2: regression -- clean FPR + S1-S8 under the hardened check ------------------------
    log.ckpt("regression: clean FPR and S1-S8 under the hardened check", 2, 3)
    fp = []
    for stem in blocks:
        e = reg[stem]; ks = (e.get("tamperable_sites", {}) or {}).get("key_schedule", []) or []
        if cg((MODELS_DIR / f"{stem}.py").read_text(), stem, ks, harden=True):
            fp.append(stem)
    log.info(f"  clean FPR (hardened): {len(fp)}/{len(blocks)}  {fp if fp else ''}")
    caught = {s: 0 for s in STYLES}; tot = {s: 0 for s in STYLES}
    for stem in blocks:
        e = reg[stem]; block, key = e["block_size"], e["key_size"]
        ts_sites = e.get("tamperable_sites", {}) or {}
        ks = ts_sites.get("key_schedule", []) or []
        ctx = {"stem": stem, "block_size": block, "key_size": key, "keysched_names": ks,
               "nonlinear_fn_names": list((ts_sites.get("nonlinear_ops") or {}).keys())}
        src = (MODELS_DIR / f"{stem}.py").read_text()
        for sid, style in STYLES.items():
            tsrc, meta = style.inject(src, ctx, random.Random(7))
            if tsrc is None:
                continue
            ok, _ = validate_style(src, tsrc, stem, block, key, style, meta)
            if not ok:
                continue
            tot[sid] += 1
            if cg(tsrc, stem, ks, harden=True):
                caught[sid] += 1
    style_rates = {s: [caught[s], tot[s]] for s in STYLES if tot[s]}
    log.info(f"  S1-S8 (hardened): " + "  ".join(f"{s} {caught[s]}/{tot[s]}" for s in STYLES if tot[s]))

    # --- artifacts ------------------------------------------------------------------------------
    log.ckpt("writing artifacts", 3, 3)
    naive_evaded = sorted(set(r["id"] for r in rows if not r["naive_check"]))
    hard_evaded = sorted(set(r["id"] for r in rows if not r["hardened_check"]))
    ts = datetime.now().strftime("%Y%m%d_%H%M%S")
    outdir = ensure(REPORTS / "adaptive" / ts)
    write_json(outdir / "summary.json", {
        "timestamp": datetime.now().isoformat(timespec="seconds"),
        "adaptive_results": rows,
        "naive_evaded": naive_evaded, "hardened_evaded": hard_evaded,
        "regression": {"clean_fpr": {"flagged": len(fp), "of": len(blocks), "variants": fp},
                       "styles": style_rates},
        "wall_clock_sec": round(time.time() - t0, 2)})
    log.info(f"adaptive evasions: naive check evaded by {naive_evaded}; hardened check evaded by "
             f"{hard_evaded if hard_evaded else 'none'}")
    log.info(f"summary -> {outdir / 'summary.json'}")
    log.done(f"adaptive-evasion study in {round(time.time()-t0,2)}s")
    return 0


if __name__ == "__main__":
    sys.exit(main())
