#!/usr/bin/env python3
"""e14_literature_weakenings.py -- L2 vs literature-grounded weak S-boxes (non-circular test).

L2's headline result (RQ6) uses an S-box replaced by the identity, which is our own injector. The
fair question is whether L2 catches weak S-boxes that are NOT ours: the GOST cautionary tale is
precisely a saboteur choosing a cryptographically weak (but bijective) substitution table. Here we
substitute weak S-boxes drawn from the design literature's failure modes --- a fully linear
bijection (nonlinearity 0) and a low-nonlinearity nonlinear table --- into the SPN ciphers, and ask
whether L2 flags them. We also compute each S-box's actual nonlinearity, so the reader can see that
L2 fires because the substitution is genuinely weaker, not because of any injected signature. This
is a direct, non-circular test of the property-probe layer.

Cluster-safe, checkpoint-logged, no Isabelle / network.
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
from src.corpus.probes import probe_vector, calibrate, flags
from src.tamper.oracle import _exec_module, _find, evaluate

AEAD = ("ascon", "gift_cofb")


def nonlinearity(sbox, n=4):
    """Nonlinearity of an n-bit S-box via the Walsh-Hadamard transform. Optimal 4-bit S-boxes
    (e.g. PRESENT) reach 4; a linear/affine map has 0."""
    N = 1 << n
    par = lambda v: bin(v).count("1") & 1
    mx = 0
    for b in range(1, N):
        for a in range(N):
            wht = sum(1 if (par(a & x) ^ par(b & sbox[x])) == 0 else -1 for x in range(N))
            mx = max(mx, abs(wht))
    return (N - mx) // 2


# literature failure modes: a fully linear bijection (NL 0) and a genuinely nonlinear but weak
# bijection (NL 2), versus the optimal NL 4 of the ciphers' real S-boxes.
LINEAR_SBOX = [((x << 1) & 0xF) | (x >> 3) for x in range(16)]           # linear, bijective, NL 0
WEAK_NL_SBOX = [2, 10, 0, 14, 6, 5, 3, 8, 7, 11, 15, 1, 12, 13, 9, 4]    # nonlinear but weak, NL 2
WEAK_SBOXES = {"linear": LINEAR_SBOX, "weak_nl2": WEAK_NL_SBOX}


def replace_sbox(source: str, new_sbox) -> str | None:
    """Replace the module-level `SBOX = [...]` assignment; SBOX_INV is derived from SBOX in-source."""
    tree = ast.parse(source)
    for node in tree.body:
        if isinstance(node, ast.Assign) and any(
                isinstance(t, ast.Name) and t.id == "SBOX" for t in node.targets):
            node.value = ast.parse(repr(list(new_sbox))).body[0].value
            ast.fix_missing_locations(tree)
            return ast.unparse(tree)
    return None


def enc_of(src, stem):
    return _find(_exec_module(src, stem), stem, "encrypt")


def real_sbox(src):
    ns = {}
    exec(compile(src, "s", "exec"), ns)
    return ns.get("SBOX")


def main() -> int:
    log = get_logger("e14_literature_weakenings")
    t0 = time.time()
    reg = {read_json(p)["variant"].lower(): read_json(p) for p in REGISTRY.glob("*.json")}
    blocks = [s for s in reg if not any(s.startswith(a) for a in AEAD)]
    # SPN ciphers with a 4-bit SBOX table
    spn = [s for s in sorted(blocks) if "SBOX = [" in (MODELS_DIR / f"{s}.py").read_text()
           and reg[s]["block_size"] <= 64]

    log.ckpt("computing S-box nonlinearities (literature weak vs strong)", 1, 3)
    nl_lin = nonlinearity(LINEAR_SBOX)
    nl_weak = nonlinearity(WEAK_NL_SBOX)
    log.info(f"  weak S-box nonlinearity: linear={nl_lin}, low_nl={nl_weak} "
             f"(optimal 4-bit S-box = 4)")

    log.ckpt("calibrating clean L2 manifold and probing weak-S-box variants", 2, 3)
    clean_vecs = []
    for stem in blocks:
        e = reg[stem]
        enc = enc_of((MODELS_DIR / f"{stem}.py").read_text(), stem)
        if enc:
            clean_vecs.append(probe_vector(enc, e["block_size"], e["key_size"]))
    thr = calibrate(clean_vecs)

    rows = []
    caught = {k: 0 for k in WEAK_SBOXES}
    tot = {k: 0 for k in WEAK_SBOXES}
    for stem in spn:
        e = reg[stem]; block, key = e["block_size"], e["key_size"]
        clean_src = (MODELS_DIR / f"{stem}.py").read_text()
        strong_nl = nonlinearity(real_sbox(clean_src))
        for name, sb in WEAK_SBOXES.items():
            wsrc = replace_sbox(clean_src, sb)
            if wsrc is None:
                continue
            orc = evaluate(clean_src, wsrc, stem, block, key)
            if not orc.get("ok") or not orc.get("behavior_changed") or not orc.get("invertible"):
                continue                        # must be a real, still-bijective weakening
            enc = enc_of(wsrc, stem)
            if enc is None:
                continue
            vec = probe_vector(enc, block, key)
            fl = flags(vec, thr)
            tot[name] += 1
            if fl:
                caught[name] += 1
            rows.append({"cipher": stem, "weak_sbox": name, "strong_nl": strong_nl,
                         "weak_nl": nonlinearity(sb), "probe": vec, "flags": fl})
        log.info(f"  {stem}: strong S-box NL={strong_nl}; "
                 f"weak variants flagged: {[r['weak_sbox'] for r in rows if r['cipher']==stem and r['flags']]}")

    log.ckpt("writing artifacts", 3, 3)
    ts = datetime.now().strftime("%Y%m%d_%H%M%S")
    outdir = ensure(REPORTS / "literature_weakenings" / ts)
    write_json(outdir / "summary.json", {
        "timestamp": datetime.now().isoformat(timespec="seconds"),
        "weak_sbox_nonlinearity": {"linear": nl_lin, "low_nl": nl_weak},
        "detection": {k: {"caught": caught[k], "total": tot[k]} for k in WEAK_SBOXES},
        "n_spn_ciphers": len(spn), "results": rows,
        "wall_clock_sec": round(time.time() - t0, 2)})
    for k in WEAK_SBOXES:
        log.info(f"L2 detection, {k} weak S-box: {caught[k]}/{tot[k]}")
    log.info(f"summary -> {outdir / 'summary.json'}")
    log.done(f"literature-weakening study over {len(spn)} SPN ciphers in {round(time.time()-t0,2)}s")
    return 0


if __name__ == "__main__":
    sys.exit(main())
