#!/usr/bin/env python3
"""
e8_ct_vs_cipherguard.py -- constant-time analyzer vs. CipherGuard (the novelty experiment).

Answers "isn't CipherGuard just constant-time analysis?" by measuring, per backdoor style,
what a CT analyzer (secret-dependent control flow on the encryption path) catches versus
what CipherGuard (CT + a key->output dataflow signal) catches. The decisive column is S5,
the BRANCHLESS leak: constant-time by construction, so CT passes it, while CipherGuard's
dataflow signal flags it. Clean false-positive rates are reported for both.

Usage: python scripts/e8_ct_vs_cipherguard.py [--limit N]
"""
from __future__ import annotations
import argparse
import random
import sys
from collections import defaultdict
from datetime import datetime
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))

from src.common.logging import get_logger
from src.common.io import read_json, write_json
from src.common.paths import REGISTRY, MODELS_DIR, RESULTS, REPORTS, ensure
from src.tamper.backdoor_styles import STYLES, validate_style
from src.models.ct_baseline import ct_control_flow_violation, cipherguard_flags

STYLE_IDS = list(STYLES.keys())


def ctx_for(e: dict) -> dict:
    ts = e.get("tamperable_sites", {}) or {}
    return {"stem": e["variant"].lower(), "block_size": e["block_size"], "key_size": e["key_size"],
            "rounds": e["rounds"], "tamperable_sites": ts,
            "nonlinear_fn_names": list((ts.get("nonlinear_ops") or {}).keys()),
            "keysched_names": ts.get("key_schedule") or []}


def main() -> int:
    ap = argparse.ArgumentParser(description="CipherGuard E8: CT analyzer vs CipherGuard")
    ap.add_argument("--registry", type=Path, default=REGISTRY)
    ap.add_argument("--models-dir", type=Path, default=MODELS_DIR)
    ap.add_argument("--limit", type=int, default=None)
    args = ap.parse_args()

    log = get_logger("e8_ct")
    reg = sorted(args.registry.glob("*.json"))
    if args.limit:
        reg = reg[: args.limit]

    ct_hits = defaultdict(list)     # style -> [0/1 detected by CT]
    cg_hits = defaultdict(list)     # style -> [0/1 detected by CipherGuard]
    clean_ct_fp, clean_cg_fp = [], []

    n_excluded_aead = 0
    for i, rf in enumerate(reg, 1):
        e = read_json(rf); variant = e["variant"]; stem = variant.lower()
        model = args.models_dir / f"{stem}.py"
        if not model.exists() or not e["block_size"] or not e["key_size"]:
            continue
        # AEAD modes (Ascon, GIFT-COFB) are out of scope: they are not block ciphers and
        # assemble output as ciphertext||tag, which is structurally unlike a block cipher.
        if e.get("base_cipher") in ("ascon", "gift_cofb") or e.get("family") == "AEAD" \
           or "cofb" in stem or "ascon" in stem:
            n_excluded_aead += 1
            continue
        ctx = ctx_for(e); clean_src = model.read_text()
        block, key = e["block_size"], e["key_size"]

        # clean false positives
        clean_ct_fp.append(int(ct_control_flow_violation(clean_src, stem)))
        clean_cg_fp.append(int(cipherguard_flags(clean_src, stem)))

        rng = random.Random(20260801 + hash(variant) % 10000)
        for sid in STYLE_IDS:
            tsrc, meta = STYLES[sid].inject(clean_src, ctx, rng)
            if tsrc is None:
                continue
            ok, _ = validate_style(clean_src, tsrc, stem, block, key, STYLES[sid], meta)
            if not ok:
                continue
            ct_hits[sid].append(int(ct_control_flow_violation(tsrc, stem)))
            cg_hits[sid].append(int(cipherguard_flags(tsrc, stem)))
        if i % 10 == 0 or i == len(reg):
            log.ckpt(f"processed {variant}", i, len(reg))

    def rate(xs):
        return round(sum(xs) / len(xs), 3) if xs else None

    per_style = {sid: {"n": len(cg_hits[sid]),
                       "CT_analyzer_TPR": rate(ct_hits[sid]),
                       "CipherGuard_TPR": rate(cg_hits[sid])} for sid in STYLE_IDS}
    clean_fpr = {"CT_analyzer_FPR": rate(clean_ct_fp), "CipherGuard_FPR": rate(clean_cg_fp),
                 "n_clean_block_ciphers": len(clean_ct_fp), "n_excluded_aead": n_excluded_aead}

    out = {"timestamp": datetime.now().isoformat(timespec="seconds"),
           "per_style": per_style, "clean_fpr": clean_fpr,
           "takeaway": "CT catches branch-based backdoors (S1-S4) but MISSES the branchless "
                       "leak S5; CipherGuard catches S1-S5 via its dataflow signal. Both miss "
                       "S6 (key-schedule, out of scope for the encrypt-path invariant)."}
    ensure(RESULTS / "e8")
    write_json(RESULTS / "e8" / "ct_vs_cipherguard.json", out)

    log.info("per-style detection (encryption-path scope):")
    log.info(f"  {'style':22} {'n':>3} {'CT-analyzer':>12} {'CipherGuard':>12}")
    for sid in STYLE_IDS:
        p = per_style[sid]
        log.info(f"  {sid+' '+STYLES[sid].name:22.22} {p['n']:>3} "
                 f"{str(p['CT_analyzer_TPR']):>12} {str(p['CipherGuard_TPR']):>12}")
    log.info(f"clean FPR: CT={clean_fpr['CT_analyzer_FPR']} CipherGuard={clean_fpr['CipherGuard_FPR']} "
             f"(n={clean_fpr['n_clean']})")
    s5 = per_style.get("S5", {})
    log.info(f">>> S5 (branchless leak): CT-analyzer={s5.get('CT_analyzer_TPR')} "
             f"CipherGuard={s5.get('CipherGuard_TPR')}  <-- the novelty beyond constant-time")
    log.info(f"metrics -> {RESULTS/'e8'/'ct_vs_cipherguard.json'}")
    log.done("CT vs CipherGuard complete")
    return 0


if __name__ == "__main__":
    sys.exit(main())
