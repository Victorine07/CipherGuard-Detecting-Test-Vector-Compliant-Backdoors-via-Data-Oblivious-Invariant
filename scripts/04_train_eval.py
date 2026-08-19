#!/usr/bin/env python3
"""
04_train_eval.py -- CipherGuard Stage 04: detector + go/no-go gate.


  E0  in-distribution detection            (split_random)           -> sanity floor
  E1  MONEY: caught despite passing tests  (split_tamper_holdoutT6) -> tv-only vs us
  E2  detect an UNSEEN tamper type (T6)    (split_tamper_holdoutT6) -> generalization
  E3  cross-architecture (held-out SPN)    (split_family_holdoutSPN)-> bonus

Two detectors: supervised logistic (tampered-vs-clean) and one-class (clean-only
anomaly). Baselines: test-vector-only, invertibility-only. Outputs metrics.json,
per-experiment predictions, a report, and a printed GATE verdict.

"""
from __future__ import annotations
import argparse
import sys
from datetime import datetime
from pathlib import Path

import numpy as np

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))

from src.common.logging import get_logger
from src.common.io import read_json, write_json
from src.common.paths import DATASETS, RESULTS, REPORTS, ensure
from src.common.seed import set_seed
from src.models.readout import readout
from src.models.detector import Standardizer, LogisticDetector, OneClassDetector
from src.models.metrics import auroc, threshold_metrics

SPLITS = DATASETS / "splits"


def load_features(index: dict, log):
    X, meta = {}, {}
    for iid, m in index.items():
        g = read_json(Path(m["graph_path"]))
        X[iid] = readout(g)
        meta[iid] = m
    log.info(f"featurized {len(X)} items (dim={len(next(iter(X.values())))})")
    return X, meta


def arrays(ids, X, meta):
    ids = [i for i in ids if i in X]
    Xa = np.array([X[i] for i in ids])
    y = np.array([meta[i]["is_tampered"] for i in ids])
    return ids, Xa, y


def by_difficulty_tpr(ids, y, pred, meta):
    out = {}
    for tier in ("easy", "hard"):
        idx = [k for k, i in enumerate(ids) if meta[i]["is_tampered"] and meta[i]["difficulty"] == tier]
        if idx:
            t = sum(pred[k] for k in idx)
            out[tier] = {"tpr": round(t / len(idx), 3), "n": len(idx)}
    return out


def _youden_threshold(scores, y):
    """Pick the operating threshold on TRAIN that maximizes TPR - FPR."""
    best_t, best_j = 0.5, -1.0
    for t in np.unique(scores):
        pred = (scores >= t).astype(int)
        tp = np.sum((pred == 1) & (y == 1)); fn = np.sum((pred == 0) & (y == 1))
        fp = np.sum((pred == 1) & (y == 0)); tn = np.sum((pred == 0) & (y == 0))
        tpr = tp / (tp + fn) if (tp + fn) else 0.0
        fpr = fp / (fp + tn) if (fp + tn) else 0.0
        if tpr - fpr > best_j:
            best_j, best_t = tpr - fpr, t
    return best_t


def run_supervised(train_ids, test_ids, X, meta, seed):
    tr_ids, Xtr, ytr = arrays(train_ids, X, meta)
    te_ids, Xte, yte = arrays(test_ids, X, meta)
    std = Standardizer().fit(Xtr)
    clf = LogisticDetector(seed=seed).fit(std.transform(Xtr), ytr)
    thr = _youden_threshold(clf.score(std.transform(Xtr)), ytr)   # threshold from train only
    s = clf.score(std.transform(Xte))
    pred = (s >= thr).astype(int)
    return te_ids, yte, s, pred


def run_oneclass(train_ids, test_ids, X, meta):
    tr_ids, Xtr, ytr = arrays(train_ids, X, meta)
    te_ids, Xte, yte = arrays(test_ids, X, meta)
    Xclean = Xtr[ytr == 0]
    std = Standardizer().fit(Xclean)
    oc = OneClassDetector(quantile=0.99).fit(std.transform(Xclean))
    Xte_s = std.transform(Xte)
    s = oc.score(Xte_s)
    pred = oc.predict(Xte_s)
    return te_ids, yte, s, pred


def baseline_preds(test_ids, meta, kind):
    """test-vector-only / invertibility-only: flag tampered only when the property fails."""
    p = []
    for i in test_ids:
        if kind == "tv":
            p.append(0 if meta[i].get("passes_test_vector", True) else 1)
        else:
            p.append(0 if meta[i].get("invertible", True) else 1)
    return np.array(p)


def main() -> int:
    ap = argparse.ArgumentParser(description="CipherGuard Stage 04: detector + gate")
    ap.add_argument("--seed", type=int, default=20260730)
    args = ap.parse_args()
    set_seed(args.seed)

    log = get_logger("04_train_eval")
    index = read_json(SPLITS / "index.json")
    X, meta = load_features(index, log)

    def fold(name, which):
        m = read_json(SPLITS / f"{name}.json")
        return [i for i, f in m.items() if f == which]

    results = {}

    # ---------------- E0: in-distribution detection (split_random)
    tr, te = fold("split_random", "train"), fold("split_random", "test")
    ids, y, s, pred = run_supervised(tr, te, X, meta, args.seed)
    e0 = {"auroc": round(auroc(s, y), 3), **threshold_metrics(y, pred),
          "by_difficulty": by_difficulty_tpr(ids, y, pred, meta)}
    results["E0_in_distribution"] = e0
    log.info(f"E0 (split_random): AUROC={e0['auroc']} TPR={e0['tpr']} FPR={e0['fpr']} "
             f"by_diff={e0['by_difficulty']}")

    # ---------------- E1 + E2: held-out T6 (split_tamper_holdoutT6)
    tr, te = fold("split_tamper_holdoutT6", "train"), fold("split_tamper_holdoutT6", "test")
    sup_ids, sup_y, sup_s, sup_pred = run_supervised(tr, te, X, meta, args.seed)
    oc_ids, oc_y, oc_s, oc_pred = run_oneclass(tr, te, X, meta)
    tv_pred = baseline_preds(sup_ids, meta, "tv")
    inv_pred = baseline_preds(sup_ids, meta, "inv")

    def t6_recall(ids, pred):
        idx = [k for k, i in enumerate(ids) if meta[i]["tamper_type"] == "T6"]
        return round(sum(pred[k] for k in idx) / max(1, len(idx)), 3), len(idx)

    sup_rec, n_t6 = t6_recall(sup_ids, sup_pred)
    oc_rec, _ = t6_recall(oc_ids, oc_pred)
    tv_rec, _ = t6_recall(sup_ids, tv_pred)
    inv_rec, _ = t6_recall(sup_ids, inv_pred)
    e2 = {
        "n_T6_test": n_t6,
        "supervised": {"auroc": round(auroc(sup_s, sup_y), 3), **threshold_metrics(sup_y, sup_pred)},
        "oneclass": {"auroc": round(auroc(oc_s, oc_y), 3), **threshold_metrics(oc_y, oc_pred)},
    }
    e1 = {"description": "recall on T6 items that PASS the test vector",
          "test_vector_only": tv_rec, "invertibility_only": inv_rec,
          "supervised_detector": sup_rec, "oneclass_detector": oc_rec,
          "n_T6": n_t6}
    results["E1_money"] = e1
    results["E2_holdout_T6"] = e2
    log.info(f"E1 (money): T6 recall  tv_only={tv_rec}  inv_only={inv_rec}  "
             f"supervised={sup_rec}  oneclass={oc_rec}  (n_T6={n_t6})")
    log.info(f"E2 (held-out T6): supervised TPR={e2['supervised']['tpr']} FPR={e2['supervised']['fpr']} "
             f"| oneclass TPR={e2['oneclass']['tpr']} FPR={e2['oneclass']['fpr']}")

    # ---------------- E3: held-out family (split_family_holdoutSPN)
    tr, te = fold("split_family_holdoutSPN", "train"), fold("split_family_holdoutSPN", "test")
    ids, y, s, pred = run_supervised(tr, te, X, meta, args.seed)
    _, y2, s2, pred2 = run_oneclass(tr, te, X, meta)
    e3 = {"supervised": {"auroc": round(auroc(s, y), 3), **threshold_metrics(y, pred),
                         "by_difficulty": by_difficulty_tpr(ids, y, pred, meta)},
          "oneclass": {"auroc": round(auroc(s2, y2), 3), **threshold_metrics(y2, pred2)}}
    results["E3_holdout_SPN"] = e3
    log.info(f"E3 (held-out SPN): supervised AUROC={e3['supervised']['auroc']} "
             f"TPR={e3['supervised']['tpr']} FPR={e3['supervised']['fpr']}")

    # ---------------- GATE verdict
    best_t6 = max(sup_rec, oc_rec)
    e1_pass = (tv_rec == 0.0) and (best_t6 >= 0.6)
    e2_pass = best_t6 >= 0.6 and min(e2["supervised"]["fpr"], e2["oneclass"]["fpr"]) <= 0.34
    gate = {"E1_pass": bool(e1_pass), "E2_pass": bool(e2_pass),
            "best_T6_recall": best_t6, "tv_only_T6_recall": tv_rec,
            "verdict": "PROCEED" if (e1_pass and e2_pass) else "DIAGNOSE"}
    results["GATE"] = gate

    ensure(RESULTS / "gate")
    write_json(RESULTS / "gate" / "metrics.json",
               {"timestamp": datetime.now().isoformat(timespec="seconds"),
                "seed": args.seed, "results": results})
    ts_dir = ensure(REPORTS / "gate" / datetime.now().strftime("%Y%m%d_%H%M%S"))
    _write_report(ts_dir / "report.md", results)
    log.info(f"metrics -> {RESULTS/'gate'/'metrics.json'}")
    log.info(f"report  -> {ts_dir/'report.md'}")
    log.info("=" * 60)
    log.info(f"GATE: E1={'PASS' if e1_pass else 'FAIL'}  E2={'PASS' if e2_pass else 'FAIL'}  "
             f"=> {gate['verdict']}  (best T6 recall={best_t6} vs tv-only={tv_rec})")
    log.info("=" * 60)
    log.done("gate evaluation complete")
    return 0


def _write_report(path: Path, r: dict) -> None:
    L = ["# CipherGuard -- Phase 4 gate report", "",
         f"**Verdict: {r['GATE']['verdict']}**  (E1={'PASS' if r['GATE']['E1_pass'] else 'FAIL'}, "
         f"E2={'PASS' if r['GATE']['E2_pass'] else 'FAIL'})", "",
         "## E0 -- in-distribution detection (split_random)",
         f"- AUROC {r['E0_in_distribution']['auroc']}, TPR {r['E0_in_distribution']['tpr']}, "
         f"FPR {r['E0_in_distribution']['fpr']}, by-difficulty {r['E0_in_distribution']['by_difficulty']}",
         "", "## E1 -- MONEY: catching tampers that pass the test vector",
         "| detector | T6 recall |", "|---|---|",
         f"| test-vector-only | {r['E1_money']['test_vector_only']} |",
         f"| invertibility-only | {r['E1_money']['invertibility_only']} |",
         f"| supervised (graph) | {r['E1_money']['supervised_detector']} |",
         f"| one-class (clean-only) | {r['E1_money']['oneclass_detector']} |",
         f"\n> All {r['E1_money']['n_T6']} test tampers PASS the test vector and are invertible, "
         "so the formal baselines are blind to them by construction.", "",
         "## E2 -- detect an unseen tamper type (T6 never in training)",
         f"- supervised: AUROC {r['E2_holdout_T6']['supervised']['auroc']}, "
         f"TPR {r['E2_holdout_T6']['supervised']['tpr']}, FPR {r['E2_holdout_T6']['supervised']['fpr']}",
         f"- one-class:  AUROC {r['E2_holdout_T6']['oneclass']['auroc']}, "
         f"TPR {r['E2_holdout_T6']['oneclass']['tpr']}, FPR {r['E2_holdout_T6']['oneclass']['fpr']}",
         "", "## E3 -- held-out family (train ARX+Feistel, test SPN)",
         f"- supervised: AUROC {r['E3_holdout_SPN']['supervised']['auroc']}, "
         f"TPR {r['E3_holdout_SPN']['supervised']['tpr']}, FPR {r['E3_holdout_SPN']['supervised']['fpr']}, "
         f"by-difficulty {r['E3_holdout_SPN']['supervised']['by_difficulty']}",
         f"- one-class:  AUROC {r['E3_holdout_SPN']['oneclass']['auroc']}, "
         f"TPR {r['E3_holdout_SPN']['oneclass']['tpr']}, FPR {r['E3_holdout_SPN']['oneclass']['fpr']}"]
    path.write_text("\n".join(L))


if __name__ == "__main__":
    sys.exit(main())
