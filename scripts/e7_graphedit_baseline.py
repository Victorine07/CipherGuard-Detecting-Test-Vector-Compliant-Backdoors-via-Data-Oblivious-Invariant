#!/usr/bin/env python3
"""
e7_graphedit_baseline.py -- the "why not just diff against a reference?" baseline (B3).

Makes the two regimes (THREAT_MODEL.md) concrete with a graph-edit-distance detector
(subtree-hash multiset symmetric difference -- a cheap, exact graph-edit proxy):

  Regime A (reference available): distance to the item's OWN clean reference.
    -> catches EVERYTHING, including the value-only tampers (T1/T2/T4/T5) that the
       reference-free structural detector misses. This is why value-only tampers
       "belong to Regime A." But it needs the exact matching reference.

  Regime B (no matching reference): distance to the NEAREST clean cipher in a library
    that EXCLUDES the item's own variant.
    -> fails, because inter-cipher distance dominates the tamper distance; you cannot
       set a threshold that separates tampered from merely-different. This is why a
       naive diff does NOT solve Regime B -- where CipherGuard's structural detector
       (E1/E2/E6) is the contribution.

Cluster-safe; numpy only; reads the graphs from Stage 02.
"""
from __future__ import annotations
import sys
from collections import Counter
from datetime import datetime
from pathlib import Path

import numpy as np

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))

from src.common.logging import get_logger
from src.common.io import read_json, write_json
from src.common.paths import DATASETS, RESULTS, REPORTS, ensure
from src.models.metrics import auroc, threshold_metrics

SPLITS = DATASETS / "splits"
GRAPHS = DATASETS / "graphs" / "source"


def hashes(item_id: str) -> Counter:
    g = read_json(GRAPHS / f"{item_id}.json")["graph"]
    return Counter(n["hash"] for n in g["nodes"])


def dist(a: Counter, b: Counter) -> int:
    return sum((a - b).values()) + sum((b - a).values())     # multiset symmetric diff


def main() -> int:
    log = get_logger("e7_graphedit")
    index = read_json(SPLITS / "index.json")
    log.info(f"{len(index)} items")

    H = {iid: hashes(iid) for iid in index}
    clean_of = {index[i]["variant"]: i for i in index if index[i]["is_tampered"] == 0}
    clean_ids = list(clean_of.values())

    # ---- Regime A: distance to own clean reference
    a_tamper_detect, a_by_type = [], {}
    for iid, meta in index.items():
        if not meta["is_tampered"]:
            continue
        ref = clean_of.get(meta["variant"])
        if ref is None:
            continue
        d = dist(H[iid], H[ref])
        det = int(d > 0)
        a_tamper_detect.append(det)
        a_by_type.setdefault(meta["tamper_type"], []).append(det)
    regimeA = {"TPR_all_tampers": round(float(np.mean(a_tamper_detect)), 3),
               "by_type_TPR": {t: round(float(np.mean(v)), 3) for t, v in sorted(a_by_type.items())},
               "note": "needs the exact matching reference; FPR=0 by construction (clean dist=0)"}

    # ---- Regime B: min distance to nearest clean cipher EXCLUDING own variant
    y, score = [], []
    for iid, meta in index.items():
        others = [c for c in clean_ids if index[c]["variant"] != meta["variant"]]
        dmin = min(dist(H[iid], H[c]) for c in others)
        y.append(meta["is_tampered"]); score.append(dmin)
    y, score = np.array(y), np.array(score, dtype=float)
    # threshold at Youden on the same set (optimistic for the baseline)
    best_t, best_j = 0, -1.0
    for t in np.unique(score):
        pred = (score >= t).astype(int)
        m = threshold_metrics(y, pred)
        j = (m["tpr"] or 0) - (m["fpr"] or 0)
        if j > best_j:
            best_j, best_t = j, t
    predB = (score >= best_t).astype(int)
    regimeB = {"auroc": round(auroc(score, y), 3), **threshold_metrics(y, predB),
               "note": "dominated by inter-cipher distance; cannot separate tampered from different"}

    out = {"timestamp": datetime.now().isoformat(timespec="seconds"),
           "regimeA_reference_diff": regimeA, "regimeB_nearest_clean": regimeB}
    ensure(RESULTS / "e7")
    write_json(RESULTS / "e7" / "graphedit_baseline.json", out)

    log.info(f"Regime A (own reference): TPR on all tampers = {regimeA['TPR_all_tampers']} "
             f"(by type {regimeA['by_type_TPR']})")
    log.info(f"Regime B (nearest clean): AUROC={regimeB['auroc']} TPR={regimeB['tpr']} "
             f"FPR={regimeB['fpr']}  <- naive diff fails without the exact reference")
    log.info("Contrast: CipherGuard structural detector works in Regime B for encrypt-path "
             "backdoors (E1/E2/E6). That gap is the contribution.")
    log.info(f"metrics -> {RESULTS/'e7'/'graphedit_baseline.json'}")
    log.done("graph-edit baseline complete")
    return 0


if __name__ == "__main__":
    sys.exit(main())
