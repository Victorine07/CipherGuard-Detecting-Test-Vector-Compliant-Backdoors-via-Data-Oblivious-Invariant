#!/usr/bin/env python3
"""
03_dataset.py -- CipherGuard Stage 03: master index + leakage-free splits.

Builds the item index and three split families (DATASET.md Section 5), each with an
explicit leakage assertion. The splits are where the generalization claims live:

  split_random          i.i.d. detection baseline (E0). Grouped by VARIANT so a
                        cipher's clean + tampered items never straddle folds.
  split_tamper_holdoutT6  train on {T0..T5} of train-variants, test on {T0,T6} of
                        held-out variants -> detect an UNSEEN tamper type on UNSEEN
                        ciphers (E2). T6 never appears in training.
  split_family_holdoutSPN  train on ARX+Feistel, test on SPN -> cross-architecture
                        generalization (E3).

Fails loud if any leakage assertion trips. Cluster-safe; checkpoint-logged.
Usage: python scripts/03_dataset.py [--seed N]
"""
from __future__ import annotations
import argparse
import random
import sys
from collections import Counter, defaultdict
from datetime import datetime
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))

from src.common.logging import get_logger
from src.common.io import read_json, write_json
from src.common.paths import DATASETS, REPORTS, ensure

ITEMS_DIR = DATASETS / "items"
SPLITS_DIR = DATASETS / "splits"


def load_items():
    items = [read_json(f) for f in sorted(ITEMS_DIR.glob("*.json"))]
    for it in items:
        if "graph_path" not in it:
            raise RuntimeError(f"{it['item_id']}: no graph_path -- run 02_extract first")
    return items


def by_variant(items):
    d = defaultdict(list)
    for it in items:
        d[it["variant"]].append(it)
    return d


def counts(fold_map, items, key="fold"):
    per = defaultdict(lambda: Counter())
    idx = {it["item_id"]: it for it in items}
    for iid, fold in fold_map.items():
        it = idx[iid]
        per[fold]["n"] += 1
        per[fold]["tampered" if it["is_tampered"] else "clean"] += 1
        per[fold]["diff_" + it["difficulty"]] += 1   # prefix avoids clean/clean key clash
    return {k: dict(v) for k, v in per.items()}


# --------------------------------------------------------------------------- splits
def split_random(items, rng):
    variants = sorted({it["variant"] for it in items})
    rng.shuffle(variants)
    n = len(variants)
    tr, va = int(0.70 * n), int(0.85 * n)
    fold_of = {}
    for i, v in enumerate(variants):
        fold_of[v] = "train" if i < tr else ("val" if i < va else "test")
    m = {it["item_id"]: fold_of[it["variant"]] for it in items}
    # leakage: no variant spans folds (guaranteed by construction; assert anyway)
    vfolds = defaultdict(set)
    for it in items:
        vfolds[it["variant"]].add(m[it["item_id"]])
    leak = [v for v, fs in vfolds.items() if len(fs) > 1]
    return m, {"grouped_by": "variant", "leakage_variants": leak, "PASS": not leak}


def split_tamper_holdoutT6(items, rng):
    variants = sorted({it["variant"] for it in items})
    rng.shuffle(variants)
    cut = int(0.80 * len(variants))
    train_vars, test_vars = set(variants[:cut]), set(variants[cut:])
    m = {}
    for it in items:
        v, t = it["variant"], it["tamper_type"]
        if v in train_vars and t in ("T0", "T1", "T2", "T3", "T4", "T5"):
            m[it["item_id"]] = "train"
        elif v in test_vars and t in ("T0", "T6"):
            m[it["item_id"]] = "test"
        # else: dropped (T6 of train vars; T1-5 of test vars) to keep the holdout clean
    # leakage: T6 must not be in train; variants disjoint
    t6_in_train = any(m.get(it["item_id"]) == "train" and it["tamper_type"] == "T6" for it in items)
    idx = {it["item_id"]: it for it in items}
    tr_v = {idx[i]["variant"] for i, f in m.items() if f == "train"}
    te_v = {idx[i]["variant"] for i, f in m.items() if f == "test"}
    overlap = tr_v & te_v
    ok = (not t6_in_train) and (not overlap)
    return m, {"held_out_type": "T6", "train_vars": len(train_vars), "test_vars": len(test_vars),
               "t6_in_train": t6_in_train, "variant_overlap": sorted(overlap), "PASS": ok}


def split_family_holdoutSPN(items):
    m = {}
    for it in items:
        fam = it["family"]
        if fam in ("ARX", "Feistel"):
            m[it["item_id"]] = "train"
        elif fam == "SPN":
            m[it["item_id"]] = "test"
        # AEAD excluded (too few, out of core scope)
    idx = {it["item_id"]: it for it in items}
    tr_fam = {idx[i]["family"] for i, f in m.items() if f == "train"}
    te_fam = {idx[i]["family"] for i, f in m.items() if f == "test"}
    overlap = tr_fam & te_fam
    return m, {"held_out_family": "SPN", "train_families": sorted(tr_fam),
               "test_families": sorted(te_fam), "family_overlap": sorted(overlap),
               "PASS": not overlap}


def main() -> int:
    ap = argparse.ArgumentParser(description="CipherGuard Stage 03: splits")
    ap.add_argument("--seed", type=int, default=20260730)
    args = ap.parse_args()

    log = get_logger("03_dataset")
    ensure(SPLITS_DIR)
    items = load_items()
    n = len(items)
    log.info(f"loaded {n} items ({sum(i['is_tampered'] for i in items)} tampered, "
             f"{n - sum(i['is_tampered'] for i in items)} clean)")

    # master index
    index = {it["item_id"]: {
        "variant": it["variant"], "family": it["family"], "base_cipher": it["base_cipher"],
        "tamper_type": it["tamper_type"], "is_tampered": it["is_tampered"],
        "difficulty": it["difficulty"], "passes_test_vector": it.get("passes_test_vector"),
        "invertible": it.get("invertible"), "graph_path": it["graph_path"],
    } for it in items}
    write_json(SPLITS_DIR / "index.json", index)
    log.info(f"index -> {SPLITS_DIR/'index.json'}")

    rng = random.Random(args.seed)
    manifest = {"timestamp": datetime.now().isoformat(timespec="seconds"),
                "seed": args.seed, "n_items": n, "splits": {}}

    builders = {
        "split_random": lambda: split_random(items, random.Random(args.seed)),
        "split_tamper_holdoutT6": lambda: split_tamper_holdoutT6(items, random.Random(args.seed + 1)),
        "split_family_holdoutSPN": lambda: split_family_holdoutSPN(items),
    }
    all_pass = True
    for name, build in builders.items():
        m, info = build()
        write_json(SPLITS_DIR / f"{name}.json", m)
        c = counts(m, items)
        manifest["splits"][name] = {"leakage": info, "counts": c, "n_assigned": len(m)}
        status = "PASS" if info["PASS"] else "FAIL"
        all_pass &= info["PASS"]
        log.info(f"{name}: leakage_check={status} | folds={ {k: v.get('n') for k, v in c.items()} }")
        if not info["PASS"]:
            log.error(f"{name}: LEAKAGE -> {info}")

    # regime annotation (eval filter, not a fold): passes-test-vector hard subset
    regime = {iid: {"regime_A_passes_tv": bool(meta["passes_test_vector"])}
              for iid, meta in index.items() if meta["is_tampered"]}
    write_json(SPLITS_DIR / "regime.json", regime)
    manifest["regime_passes_tv_items"] = sum(1 for v in regime.values() if v["regime_A_passes_tv"])

    ts_dir = ensure(REPORTS / "dataset" / datetime.now().strftime("%Y%m%d_%H%M%S"))
    write_json(ts_dir / "manifest.json", manifest)
    log.info(f"manifest -> {ts_dir/'manifest.json'}")
    for name, s in manifest["splits"].items():
        log.info(f"  {name}: {s['counts']}")
    log.info(f"regime (passes-tv tampered items): {manifest['regime_passes_tv_items']}")

    if not all_pass:
        raise log.fail("one or more splits FAILED the leakage check")
    log.done(f"3 leakage-free splits written to {SPLITS_DIR}")
    return 0


if __name__ == "__main__":
    sys.exit(main())
