#!/usr/bin/env python3
"""
01_inject.py -- CipherGuard Stage 01: labeled tamper injection (T0-T6), with multiplicity.

For each registry variant with an executable model, emits:
  * T0 clean.
  * T1/T2/T4/T5: one item each (value-only tampers -> structurally identical graphs,
    so multiplicity would not add signal; they matter for labels / Regime A / PDV).
  * T3: up to K site-variants (linearize a nonlinear op in a rng-chosen function ->
    structurally distinct graphs).
  * T6: one item per BACKDOOR STYLE (S1..S6, src/tamper/backdoor_styles.py) -- the real
    structural diversity, aligning the training set with the E6 robustness study.

Every item passes the oracle effect-gate (no fake items). 

Usage: python scripts/01_inject.py [--limit N] [--t3-variants K] [--models-dir DIR]
"""
from __future__ import annotations
import argparse
import random
import sys
from datetime import datetime
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))

from src.common.logging import get_logger
from src.common.io import read_json, write_json, write_text
from src.common.paths import REGISTRY, MODELS_DIR, DATASETS, REPORTS, ensure
from src.tamper.taxonomy import TAXONOMY, POSITIVE_TYPES, applicable
from src.tamper.injectors import INJECTORS
from src.tamper.oracle import evaluate
from src.tamper.backdoor_styles import STYLES, BENCHMARK_STYLES, validate_style

TAMPERED_DIR = DATASETS / "tampered"
ITEMS_DIR = DATASETS / "items"
BASE_SEED = 20260729


def ctx_from_registry(entry: dict) -> dict:
    ts = entry.get("tamperable_sites", {}) or {}
    return {
        "stem": entry["variant"].lower(),
        "block_size": entry["block_size"], "key_size": entry["key_size"],
        "safe_round_margin": entry.get("safe_round_margin"),
        "nonlinear_fn_names": list((ts.get("nonlinear_ops") or {}).keys()),
        "keysched_names": ts.get("key_schedule") or [],   # needed by S6 (off-path)
    }


def item_valid(ttype: str, orc: dict) -> tuple[bool, str]:
    if not orc.get("ok"):
        return False, orc.get("error", "oracle error")
    if ttype == "T4":
        if not orc.get("behavior_changed"):
            return False, "T4 no behavioral effect"
        if not orc.get("invertible"):
            return False, "T4 not bijective"
        return True, "ok"
    if not orc.get("behavior_changed"):
        return False, f"{ttype} no behavioral effect"
    return True, "ok"


def main() -> int:
    ap = argparse.ArgumentParser(description="CipherGuard Stage 01: tamper injection")
    ap.add_argument("--registry", type=Path, default=REGISTRY)
    ap.add_argument("--models-dir", type=Path, default=MODELS_DIR)
    ap.add_argument("--t3-variants", type=int, default=3)
    ap.add_argument("--limit", type=int, default=None)
    args = ap.parse_args()

    log = get_logger("01_inject")
    ensure(TAMPERED_DIR); ensure(ITEMS_DIR)
    # clean stale items so counts are exact on re-run
    for p in list(ITEMS_DIR.glob("*.json")) + list(TAMPERED_DIR.glob("*.py")):
        p.unlink()
    log.info(f"registry={args.registry} models={args.models_dir} t3_variants={args.t3_variants}")

    reg_files = sorted(args.registry.glob("*.json"))
    if args.limit:
        reg_files = reg_files[: args.limit]
    if not reg_files:
        raise log.fail(f"no registry files under {args.registry}")
    n = len(reg_files)

    counts, by_style, by_family, by_difficulty, skips, no_model = {}, {}, {}, {}, [], []
    total = 0

    def emit(item_id, entry, ttype, style, tsrc, orc, meta, diff):
        nonlocal total
        write_text(TAMPERED_DIR / f"{item_id}.py", tsrc)
        write_json(ITEMS_DIR / f"{item_id}.json", {
            "item_id": item_id, "base_cipher": entry["base_cipher"], "variant": entry["variant"],
            "family": entry["family"], "is_tampered": 0 if ttype == "T0" else 1,
            "tamper_type": ttype, "tamper_style": style, "difficulty": diff,
            "invertible": orc.get("invertible") if orc else True,
            "passes_test_vector": orc.get("passes_test_vector") if orc else True,
            "behavior_changed": orc.get("behavior_changed") if orc else False,
            "leaks": orc.get("leaks") if orc else None,
            "injection_params": meta, "front": "source", "model_file": f"{entry['variant'].lower()}.py",
            "seed": BASE_SEED, "source_path": str(TAMPERED_DIR / f"{item_id}.py"),
            "corpus_verified": entry.get("verified"),
        })
        counts[ttype] = counts.get(ttype, 0) + 1
        if style:
            by_style[style] = by_style.get(style, 0) + 1
        by_family[entry["family"]] = by_family.get(entry["family"], 0) + 1
        by_difficulty[diff] = by_difficulty.get(diff, 0) + 1
        total += 1

    for i, rf in enumerate(reg_files, 1):
        entry = read_json(rf); variant, family = entry["variant"], entry["family"]
        stem = variant.lower()
        model = args.models_dir / f"{stem}.py"
        if not model.exists():
            no_model.append(variant); continue
        clean_src = model.read_text()
        ctx = ctx_from_registry(entry)
        block, key = ctx["block_size"], ctx["key_size"]
        if not block or not key:
            skips.append({"variant": variant, "type": "*", "reason": "missing sizes"}); continue

        emit(f"{variant}__T0", entry, "T0", None, clean_src, None, None, "clean")
        emitted = ["T0"]

        for ttype in POSITIVE_TYPES:
            if not applicable(ttype, family):
                continue

            if ttype == "T6":                                   # multiplicity: 6 benchmark styles
                for sid in BENCHMARK_STYLES:
                    style = STYLES[sid]
                    rng = random.Random(BASE_SEED + hash(variant + sid) % 100000)
                    tsrc, meta = style.inject(clean_src, ctx, rng)
                    if tsrc is None:
                        skips.append({"variant": variant, "type": f"T6/{sid}", "reason": meta.get("reason", "n/a")}); continue
                    ok, orc = validate_style(clean_src, tsrc, stem, block, key, style, meta)
                    if not ok:
                        skips.append({"variant": variant, "type": f"T6/{sid}", "reason": "invalid backdoor"}); continue
                    emit(f"{variant}__T6__{sid}", entry, "T6", sid, tsrc, orc, meta, "hard")
                    emitted.append(f"T6:{sid}")

            elif ttype == "T3":                                 # multiplicity: site variants
                seen = set()
                for k in range(args.t3_variants):
                    rng = random.Random(BASE_SEED + 1000 * k + hash(variant + "T3") % 100000)
                    tsrc, meta = INJECTORS["T3"](clean_src, ctx, rng)
                    if tsrc is None or tsrc in seen:
                        continue
                    seen.add(tsrc)
                    orc = evaluate(clean_src, tsrc, stem, block, key)
                    ok, why = item_valid("T3", orc)
                    if not ok:
                        skips.append({"variant": variant, "type": "T3", "reason": why}); continue
                    emit(f"{variant}__T3__v{len(seen)-1}", entry, "T3", None, tsrc, orc, meta, "easy")
                    emitted.append("T3")

            else:                                               # T1/T2/T4/T5 single item
                rng = random.Random(BASE_SEED + hash(variant + ttype) % 100000)
                tsrc, meta = INJECTORS[ttype](clean_src, ctx, rng)
                if tsrc is None:
                    skips.append({"variant": variant, "type": ttype, "reason": meta.get("reason", "n/a")}); continue
                orc = evaluate(clean_src, tsrc, stem, block, key)
                ok, why = item_valid(ttype, orc)
                if not ok:
                    skips.append({"variant": variant, "type": ttype, "reason": why}); continue
                emit(f"{variant}__{ttype}", entry, ttype, None, tsrc, orc, meta, TAXONOMY[ttype].difficulty)
                emitted.append(ttype)

        if i % 8 == 0 or i == n:
            log.ckpt(f"{variant} [{family}] -> {len(emitted)} items", i, n)

    ts_dir = ensure(REPORTS / "tamper" / datetime.now().strftime("%Y%m%d_%H%M%S"))
    summary = {"timestamp": datetime.now().isoformat(timespec="seconds"), "n_variants": n,
               "total_items": total, "counts_by_type": counts, "counts_by_backdoor_style": by_style,
               "by_family": by_family, "by_difficulty": by_difficulty,
               "n_skips": len(skips), "variants_without_model": no_model, "skips": skips}
    write_json(ts_dir / "counts.json", summary)
    log.info(f"items by type: {counts}")
    log.info(f"T6 by backdoor style: {by_style}")
    log.info(f"by difficulty: {by_difficulty}")
    log.info(f"total items: {total}  (skips: {len(skips)}, no-model: {len(no_model)})")
    log.info(f"counts -> {ts_dir/'counts.json'}")
    log.done(f"{total} items written to {ITEMS_DIR}")
    return 0


if __name__ == "__main__":
    sys.exit(main())
