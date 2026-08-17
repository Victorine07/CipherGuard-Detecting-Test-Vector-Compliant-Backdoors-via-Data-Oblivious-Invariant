"""Detection metrics (numpy). Threshold-free AUROC + threshold metrics."""
from __future__ import annotations
from typing import Dict

import numpy as np


def auroc(scores: np.ndarray, y: np.ndarray) -> float:
    """Rank-based AUROC (Mann-Whitney U). Returns 0.5 if a class is absent."""
    pos, neg = scores[y == 1], scores[y == 0]
    if len(pos) == 0 or len(neg) == 0:
        return float("nan")
    order = np.argsort(scores, kind="mergesort")
    ranks = np.empty(len(scores), dtype=np.float64)
    ranks[order] = np.arange(1, len(scores) + 1)
    # average ranks for ties
    _, inv, counts = np.unique(scores, return_inverse=True, return_counts=True)
    sums = np.zeros(len(counts)); np.add.at(sums, inv, ranks)
    ranks = (sums / counts)[inv]
    r_pos = ranks[y == 1].sum()
    u = r_pos - len(pos) * (len(pos) + 1) / 2.0
    return float(u / (len(pos) * len(neg)))


def threshold_metrics(y: np.ndarray, pred: np.ndarray) -> Dict[str, float]:
    tp = int(np.sum((pred == 1) & (y == 1)))
    fp = int(np.sum((pred == 1) & (y == 0)))
    tn = int(np.sum((pred == 0) & (y == 0)))
    fn = int(np.sum((pred == 0) & (y == 1)))
    tpr = tp / (tp + fn) if (tp + fn) else float("nan")
    fpr = fp / (fp + tn) if (fp + tn) else float("nan")
    prec = tp / (tp + fp) if (tp + fp) else float("nan")
    f1 = 2 * prec * tpr / (prec + tpr) if prec and tpr and not np.isnan(prec) and not np.isnan(tpr) else 0.0
    acc = (tp + tn) / max(1, len(y))
    return {"tp": tp, "fp": fp, "tn": tn, "fn": fn, "tpr": round(tpr, 3),
            "fpr": round(fpr, 3), "precision": round(prec, 3) if not np.isnan(prec) else None,
            "f1": round(f1, 3), "accuracy": round(acc, 3)}
