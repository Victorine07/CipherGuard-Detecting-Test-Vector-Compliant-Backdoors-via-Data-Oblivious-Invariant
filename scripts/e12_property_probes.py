#!/usr/bin/env python3
"""e12_property_probes.py -- CipherGuard detection layer L2 (reference-free property probes).

Calibrates a clean-cipher manifold from the verified corpus, then measures how well reference-free
cryptographic property probes detect the weakening classes that the structural check (L1) cannot
see: round reduction (T1), nonlinearity removal (T3), and S-box weakening (T4). Reports the clean
false-positive rate and per-class detection, and makes explicit the honest boundary (round
reduction is not reference-free detectable, because lightweight ciphers over-provision rounds for a
cryptanalytic margin, so they reach full diffusion well before their full round count).

Non-circular by construction: a weakened cipher fails a probe for a genuine cryptographic reason,
not because a signature was injected. Cluster-safe, checkpoint-logged, no Isabelle / network.
Usage: python scripts/e12_property_probes.py [--limit N] [--t3-sites K]
"""
from __future__ import annotations
import argparse
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
from src.tamper.injectors import INJECTORS
from src.tamper.oracle import _exec_module, _find, evaluate

AEAD_PREFIXES = ("ascon", "gift_cofb")
BASE_SEED = 20260811


def ctx_from_registry(e: dict) -> dict:
    ts = e.get("tamperable_sites", {}) or {}
    return {"stem": e["variant"].lower(), "block_size": e["block_size"], "key_size": e["key_size"],
            "safe_round_margin": e.get("safe_round_margin"),
            "nonlinear_fn_names": list((ts.get("nonlinear_ops") or {}).keys()),
            "keysched_names": ts.get("key_schedule") or []}


def enc_of(src: str, stem: str):
    ns = _exec_module(src, stem)
    return _find(ns, stem, "encrypt")


def main() -> int:
    ap = argparse.ArgumentParser(description="CipherGuard L2: reference-free property probes")
    ap.add_argument("--models-dir", type=Path, default=MODELS_DIR)
    ap.add_argument("--registry", type=Path, default=REGISTRY)
    ap.add_argument("--t3-sites", type=int, default=3)
    ap.add_argument("--limit", type=int, default=None)
    args = ap.parse_args()

    log = get_logger("e12_property_probes")
    t0 = time.time()
    reg = {read_json(p)["variant"].lower(): read_json(p) for p in args.registry.glob("*.json")}
    models = [p for p in sorted(args.models_dir.glob("*.py"))
              if not p.stem.startswith("__") and not any(p.stem.startswith(a) for a in AEAD_PREFIXES)]
    if args.limit:
        models = models[: args.limit]
    if not models:
        raise log.fail(f"no block-cipher models under {args.models_dir}")
    n = len(models)
    log.info(f"models_dir={args.models_dir}  block-cipher models={n}  (AEAD excluded)")

    # CKPT 1: probe every clean cipher and calibrate the manifold.
    log.ckpt("probing clean ciphers and calibrating the clean manifold", 1, 4)
    clean = {}
    for i, mf in enumerate(models, 1):
        stem = mf.stem
        e = reg.get(stem)
        if not e or not e.get("block_size") or not e.get("key_size"):
            continue
        enc = enc_of(mf.read_text(), stem)
        if enc is None:
            log.warn(f"no encrypt in {stem}; skipping"); continue
        clean[stem] = probe_vector(enc, e["block_size"], e["key_size"])
        if i % 10 == 0 or i == n:
            log.info(f"  probed {i}/{n} clean ciphers")
    thr = calibrate(list(clean.values()))
    log.info(f"clean manifold: diffusion_min={thr['diffusion_min']:.4f} "
             f"sac_dev_max={thr['sac_dev_max']:.4f} affine_max={thr['affine_max']:.6g}")
    log.info(f"thresholds: diffusion<{thr['diffusion_thresh']:.4f}  "
             f"|sac-0.5|>{thr['sac_dev_thresh']:.4f}  affine>{thr['affine_thresh']:.4g}")

    # CKPT 2: clean false-positive rate.
    log.ckpt("measuring clean false-positive rate under the calibrated thresholds", 2, 4)
    clean_fp = [s for s, v in clean.items() if flags(v, thr)]
    log.info(f"clean FPR: {len(clean_fp)}/{len(clean)}  "
             f"({'0' if not clean_fp else 'flagged: ' + ', '.join(clean_fp)})")

    # CKPT 3: per-class detection on the weakenings L1 cannot see.
    # Consume the SAME benchmark items as the injected dataset (datasets/items + datasets/tampered),
    # so the L2 weakening counts (T1/T3/T4) match Table~\ref{tab:dataset} exactly rather than
    # re-injecting a differently-sized set.
    log.ckpt("probing benchmark weakenings (T1/T3/T4) and measuring L2 detection", 3, 4)
    caught = {"T1": 0, "T3": 0, "T4": 0}
    total = {"T1": 0, "T3": 0, "T4": 0}
    per_item = []
    items_dir = args.registry.parent / "items"
    tampered_dir = args.registry.parent / "tampered"
    processed = 0
    for f in sorted(items_dir.glob("*.json")):
        it = read_json(f)
        ttype = it.get("tamper_type")
        if ttype not in ("T1", "T3", "T4"):
            continue
        stem = it["variant"].lower()
        if any(stem.startswith(a) for a in AEAD_PREFIXES) or stem not in clean:
            continue
        e = reg.get(stem)
        block, key = e["block_size"], e["key_size"]
        src_path = tampered_dir / f"{it['item_id']}.py"
        if not src_path.exists():
            log.warn(f"missing tampered source for {it['item_id']}; skipping"); continue
        enc = enc_of(src_path.read_text(), stem)
        if enc is None:
            continue
        vec = probe_vector(enc, block, key)
        fl = flags(vec, thr)
        total[ttype] += 1
        if fl:
            caught[ttype] += 1
        per_item.append({"item_id": it.get("item_id"), "variant": stem, "tamper": ttype,
                         "probe": vec, "flags": fl})
        processed += 1
        if processed % 20 == 0:
            log.info(f"  processed {processed} items  (T1 {caught['T1']}/{total['T1']}, "
                     f"T3 {caught['T3']}/{total['T3']}, T4 {caught['T4']}/{total['T4']})")
    log.info(f"  final counts: T1 {caught['T1']}/{total['T1']}, "
             f"T3 {caught['T3']}/{total['T3']}, T4 {caught['T4']}/{total['T4']}")

    # CKPT 4: artifacts.
    log.ckpt("writing artifacts", 4, 4)
    def rate(t):
        return round(caught[t] / total[t], 4) if total[t] else None
    ts = datetime.now().strftime("%Y%m%d_%H%M%S")
    summary = {
        "timestamp": datetime.now().isoformat(timespec="seconds"),
        "n_clean_block_ciphers": len(clean),
        "clean_fpr": {"flagged": len(clean_fp), "of": len(clean), "variants": clean_fp},
        "thresholds": thr,
        "detection": {t: {"caught": caught[t], "total": total[t], "rate": rate(t)}
                      for t in ("T1", "T3", "T4")},
        "wall_clock_sec": round(time.time() - t0, 2),
        "per_item": per_item,
    }
    outdir = ensure(REPORTS / "probes" / ts)
    write_json(outdir / "summary.json", summary)
    log.info(f"L2 detection  T4 (S-box weakening): {caught['T4']}/{total['T4']} ({rate('T4')})")
    log.info(f"L2 detection  T3 (nonlinearity removal): {caught['T3']}/{total['T3']} ({rate('T3')})")
    log.info(f"L2 detection  T1 (round reduction): {caught['T1']}/{total['T1']} ({rate('T1')})  "
             f"-- expected ~0: reduced-round ciphers still reach full diffusion")
    log.info(f"clean FPR under calibrated thresholds: {len(clean_fp)}/{len(clean)}")
    log.info(f"summary -> {outdir / 'summary.json'}")
    log.done(f"L2 probe study over {len(clean)} clean ciphers in {summary['wall_clock_sec']}s")
    return 0


if __name__ == "__main__":
    sys.exit(main())
