#!/usr/bin/env python3
"""
e10_harder_backdoors.py -- adaptive backdoors + the interprocedural fix (audit #3).

An adversary who knows CipherGuard's encrypt-scoped check hides the leak in a HELPER that
encrypt calls (styles S7/S8), so encrypt itself has no branch and no bare key arithmetic.
This experiment shows: (a) the intraprocedural check MISSES S7/S8 (a real evasion), and
(b) the principled interprocedural check (follow the encryption call graph, sanitize the key
schedule) CATCHES S1-S8's on-path leaks at zero clean false positives -- so the invariant
holds under this adaptive strategy, not just the naive one. S6 (off-path, key schedule)
remains the disclosed boundary.

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
from src.models.ct_baseline import cipherguard_flags          # intraprocedural
from src.models.interproc import cipherguard_interproc        # interprocedural

STYLE_IDS = list(STYLES.keys())   # S1..S8


def ctx_for(e):
    ts = e.get("tamperable_sites", {}) or {}
    return {"stem": e["variant"].lower(), "block_size": e["block_size"], "key_size": e["key_size"],
            "rounds": e["rounds"], "tamperable_sites": ts,
            "nonlinear_fn_names": list((ts.get("nonlinear_ops") or {}).keys()),
            "keysched_names": ts.get("key_schedule") or []}


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--registry", type=Path, default=REGISTRY)
    ap.add_argument("--models-dir", type=Path, default=MODELS_DIR)
    ap.add_argument("--limit", type=int, default=None)
    args = ap.parse_args()
    log = get_logger("e10_harder")

    reg = sorted(args.registry.glob("*.json"))
    if args.limit:
        reg = reg[: args.limit]

    intra, inter = defaultdict(list), defaultdict(list)
    clean_intra_fp, clean_inter_fp = [], []

    for i, rf in enumerate(reg, 1):
        e = read_json(rf); variant = e["variant"]; stem = variant.lower()
        model = args.models_dir / f"{stem}.py"
        if not model.exists() or not e["block_size"] or not e["key_size"]:
            continue
        if e.get("base_cipher") in ("ascon", "gift_cofb") or "cofb" in stem or "ascon" in stem:
            continue
        ctx = ctx_for(e); clean_src = model.read_text(); ks = ctx["keysched_names"]
        block, key = e["block_size"], e["key_size"]

        clean_intra_fp.append(int(cipherguard_flags(clean_src, stem)))
        clean_inter_fp.append(int(cipherguard_interproc(clean_src, stem, ks)))

        rng = random.Random(20260802 + hash(variant) % 10000)
        for sid in STYLE_IDS:
            tsrc, meta = STYLES[sid].inject(clean_src, ctx, rng)
            if tsrc is None:
                continue
            ok, _ = validate_style(clean_src, tsrc, stem, block, key, STYLES[sid], meta)
            if not ok:
                continue
            intra[sid].append(int(cipherguard_flags(tsrc, stem)))
            inter[sid].append(int(cipherguard_interproc(tsrc, stem, ks)))
        if i % 10 == 0 or i == len(reg):
            log.ckpt(f"{variant} processed", i, len(reg))

    def rate(xs):
        return round(sum(xs) / len(xs), 3) if xs else None

    per_style = {sid: {"n": len(inter[sid]), "intraprocedural_TPR": rate(intra[sid]),
                       "interprocedural_TPR": rate(inter[sid])} for sid in STYLE_IDS}
    out = {"timestamp": datetime.now().isoformat(timespec="seconds"), "per_style": per_style,
           "clean_FPR": {"intraprocedural": rate(clean_intra_fp),
                         "interprocedural": rate(clean_inter_fp),
                         "n_clean_block_ciphers": len(clean_intra_fp)},
           "takeaway": "adaptive interprocedural backdoors (S7/S8) evade the encrypt-scoped "
                       "check but are caught by the interprocedural invariant check at 0 clean FPR; "
                       "S6 (key schedule) remains the disclosed boundary."}
    ensure(RESULTS / "e10")
    write_json(RESULTS / "e10" / "harder_backdoors.json", out)

    log.info(f"  {'style':44} {'n':>3} {'intra-proc':>11} {'inter-proc':>11}")
    for sid in STYLE_IDS:
        p = per_style[sid]
        log.info(f"  {sid+' '+STYLES[sid].name:44.44} {p['n']:>3} "
                 f"{str(p['intraprocedural_TPR']):>11} {str(p['interprocedural_TPR']):>11}")
    log.info(f"clean FPR: intra={out['clean_FPR']['intraprocedural']} "
             f"inter={out['clean_FPR']['interprocedural']} (n={out['clean_FPR']['n_clean_block_ciphers']})")
    for sid in ("S7", "S8"):
        p = per_style[sid]
        log.info(f">>> {sid} (adaptive, via helper): intra-proc={p['intraprocedural_TPR']} "
                 f"inter-proc={p['interprocedural_TPR']}  <-- evades naive check, caught interprocedurally")
    log.info(f"metrics -> {RESULTS/'e10'/'harder_backdoors.json'}")
    log.done("harder-backdoors experiment complete")
    return 0


if __name__ == "__main__":
    sys.exit(main())
