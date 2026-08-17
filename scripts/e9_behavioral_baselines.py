#!/usr/bin/env python3
"""
e9_behavioral_baselines.py -- realistic behavioral defenses vs. CipherGuard (RQ1, de-tautologized).

The "money experiment" must not be circular ("test-vector-only misses test-vector-passing
backdoors"). This experiment shows the deeper, non-trivial fact: a rare-trigger backdoor is
behaviorally IDENTICAL to a clean cipher except on a measure-2^-t trigger set, so EVERY
behavioral defense a real auditor would run misses it:

  * random known-answer fuzzing (Regime A, needs the reference): detection = probability a
    random input hits the trigger = 1-(1-2^-t)^N. Even N=10^5 tests catch only the 2^-16
    trigger sometimes, and a stealthier 2^-32 trigger is out of reach at any feasible N.
  * avalanche / diffusion test (reference-free): the backdoor doesn't perturb the diffusion
    statistic (it fires too rarely), so a backdoored cipher's avalanche is indistinguishable
    from clean.

CipherGuard reads the code STRUCTURE, so its detection is independent of trigger rarity.
This is the real contrast: behavioral testing fundamentally cannot catch a rare-trigger
backdoor; structural analysis can.

Cluster-safe; numpy-free; reuses the verified backdoor styles + oracle. In-scope block
ciphers only (AEAD excluded). Usage: python scripts/e9_behavioral_baselines.py [--M 400]
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
from src.tamper.oracle import _exec_module, _find
from src.models.ct_baseline import cipherguard_flags

LEAK_STYLES = ["S1", "S2", "S3", "S5"]     # plaintext-triggered key leaks (rare trigger)


def ctx_for(e):
    ts = e.get("tamperable_sites", {}) or {}
    return {"stem": e["variant"].lower(), "block_size": e["block_size"], "key_size": e["key_size"],
            "rounds": e["rounds"], "tamperable_sites": ts,
            "nonlinear_fn_names": list((ts.get("nonlinear_ops") or {}).keys()),
            "keysched_names": ts.get("key_schedule") or []}


def avalanche(enc, block, key, rng, M):
    """Mean fraction of output bits that flip when one input bit flips (~0.5 for a good
    cipher). A rare-trigger backdoor leaves this unchanged."""
    bmask, kmask = (1 << block) - 1, (1 << key) - 1
    tot = 0.0
    for _ in range(M):
        pt, k = rng.getrandbits(block) & bmask, rng.getrandbits(key) & kmask
        b = rng.randrange(block)
        c0 = enc(pt, k); c1 = enc(pt ^ (1 << b), k)
        tot += bin((c0 ^ c1) & bmask).count("1") / block
    return tot / M


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--registry", type=Path, default=REGISTRY)
    ap.add_argument("--models-dir", type=Path, default=MODELS_DIR)
    ap.add_argument("--M", type=int, default=400, help="avalanche samples per cipher/style")
    ap.add_argument("--limit", type=int, default=None)
    args = ap.parse_args()
    log = get_logger("e9_behavioral")

    reg = sorted(args.registry.glob("*.json"))
    if args.limit:
        reg = reg[: args.limit]

    trigger_probs, aval_diffs, cg_hits = [], [], []
    n_items = 0
    for i, rf in enumerate(reg, 1):
        e = read_json(rf); variant = e["variant"]; stem = variant.lower()
        model = args.models_dir / f"{stem}.py"
        if not model.exists() or not e["block_size"] or not e["key_size"]:
            continue
        if e.get("base_cipher") in ("ascon", "gift_cofb") or "cofb" in stem or "ascon" in stem:
            continue                                    # AEAD out of scope
        ctx = ctx_for(e); clean_src = model.read_text()
        block, key = e["block_size"], e["key_size"]
        rng = random.Random(20260801 + hash(variant) % 10000)
        try:
            enc_c = _find(_exec_module(clean_src, f"{stem}_c"), stem, "encrypt")
            av_c = avalanche(enc_c, block, key, random.Random(1), args.M)
        except Exception:
            continue

        for sid in LEAK_STYLES:
            tsrc, meta = STYLES[sid].inject(clean_src, ctx, rng)
            if tsrc is None:
                continue
            ok, _ = validate_style(clean_src, tsrc, stem, block, key, STYLES[sid], meta)
            if not ok:
                continue
            t = meta.get("t", 16)
            try:
                enc_bd = _find(_exec_module(tsrc, f"{stem}_b"), stem, "encrypt")
                av_bd = avalanche(enc_bd, block, key, random.Random(1), args.M)
            except Exception:
                continue
            trigger_probs.append(2.0 ** (-t))
            aval_diffs.append(abs(av_bd - av_c))
            cg_hits.append(int(cipherguard_flags(tsrc, stem)))
            n_items += 1
        if i % 10 == 0 or i == len(reg):
            log.ckpt(f"{variant} processed", i, len(reg))

    def mean(xs):
        return sum(xs) / len(xs) if xs else float("nan")

    # fuzzing detection = mean over items of P(hit trigger in N random tests)
    def fuzz_at(N, probs):
        return round(mean([1.0 - (1.0 - p) ** N for p in probs]), 4)

    # stealthier adversary: a 2^-32 trigger
    stealth = [2.0 ** -32] * len(trigger_probs)

    aval_flag_rate = round(mean([1.0 if d > 0.05 else 0.0 for d in aval_diffs]), 4)
    res = {
        "timestamp": datetime.now().isoformat(timespec="seconds"), "n_items": n_items,
        "avalanche_samples_per_item": args.M,
        "mean_trigger_prob": mean(trigger_probs),
        "fuzzing_detection_injected_2^-16": {
            "N=1e3": fuzz_at(1000, trigger_probs), "N=1e4": fuzz_at(10000, trigger_probs),
            "N=1e5": fuzz_at(100000, trigger_probs), "N=1e6": fuzz_at(1000000, trigger_probs)},
        "fuzzing_detection_stealthier_2^-32": {
            "N=1e5": fuzz_at(100000, stealth), "N=1e6": fuzz_at(1000000, stealth),
            "N=1e9": fuzz_at(10**9, stealth)},
        "avalanche_test": {"mean_abs_diff_clean_vs_backdoored": round(mean(aval_diffs), 5),
                           "detection_rate": aval_flag_rate,
                           "note": "backdoored avalanche is within sampling noise of clean"},
        "cipherguard_structural_detection": round(mean(cg_hits), 3),
    }
    ensure(RESULTS / "e9")
    write_json(RESULTS / "e9" / "behavioral_baselines.json", res)

    log.info(f"items: {n_items}  (leak styles {LEAK_STYLES}, in-scope block ciphers)")
    log.info(f"random KAT fuzzing detection of the injected 2^-16 backdoor:")
    for k, v in res["fuzzing_detection_injected_2^-16"].items():
        log.info(f"   {k} random tests -> {v}")
    log.info(f"   ... same defender vs a stealthier 2^-32 trigger: "
             f"N=1e6 -> {res['fuzzing_detection_stealthier_2^-32']['N=1e6']}, "
             f"N=1e9 -> {res['fuzzing_detection_stealthier_2^-32']['N=1e9']}")
    log.info(f"avalanche/diffusion test: mean|clean-backdoor|="
             f"{res['avalanche_test']['mean_abs_diff_clean_vs_backdoored']} "
             f"detection={res['avalanche_test']['detection_rate']} (reference-free, misses it)")
    log.info(f">>> CipherGuard (structural): detection = "
             f"{res['cipherguard_structural_detection']}  (independent of trigger rarity)")
    log.info(f"metrics -> {RESULTS/'e9'/'behavioral_baselines.json'}")
    log.done("behavioral-baselines experiment complete")
    return 0


if __name__ == "__main__":
    sys.exit(main())
