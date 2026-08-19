#!/usr/bin/env python3
"""
05_train_gat.py -- CipherGuard Phase 5: train/evaluate the Hybrid GAT+MLP (GPU cluster).

Replaces the numpy readout (Stage 04) with the real graph model, run across the
leakage-free splits, multi-seed, with mean +/- std. Requires torch + torch_geometric
(requirements-gpu.txt); on a box without them it prints setup instructions and exits 0.

Usage (cluster): python scripts/05_train_gat.py --epochs 150 --seeds 5
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
from src.common.paths import DATASETS, RESULTS, REPORTS, CHECKPOINTS, ensure
from src.models.metrics import auroc, threshold_metrics

SPLITS = DATASETS / "splits"
GRAPHS = DATASETS / "graphs" / "source"
STUDY_SPLITS = ["split_random", "split_tamper_holdoutT6", "split_family_holdoutSPN"]


def _torch_ok():
    try:
        import torch  # noqa
        import torch_geometric  # noqa
        return True
    except Exception:
        return False


def _fold(name, which):
    m = read_json(SPLITS / f"{name}.json")
    return [i for i, f in m.items() if f == which]


def _youden(scores, y):
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


def train_one(split, seed, args, log):
    import torch
    from src.models.gat import (CipherGraphDataset, HybridGAT, loss_fn, make_loader,
                                 TAMPER_TYPES)
    from src.extraction.graph import NODE_DIM
    from src.extraction.pdv import PDV_DIM

    torch.manual_seed(seed); np.random.seed(seed)
    device = torch.device("cuda" if torch.cuda.is_available() else "cpu")

    tr_ids, te_ids = _fold(split, "train"), _fold(split, "test")
    va_ids = _fold(split, "val") or tr_ids[: max(1, len(tr_ids) // 6)]
    tr = CipherGraphDataset(GRAPHS, tr_ids)
    va = CipherGraphDataset(GRAPHS, va_ids)
    te = CipherGraphDataset(GRAPHS, te_ids)
    tl = make_loader(tr, args.batch_size, True)
    vl = make_loader(va, args.batch_size, False)
    el = make_loader(te, args.batch_size, False)

    model = HybridGAT(NODE_DIM, PDV_DIM, hidden=args.hidden, heads=args.heads).to(device)
    opt = torch.optim.Adam(model.parameters(), lr=args.lr, weight_decay=1e-4)

    best_val, best_state, patience = -1.0, None, 0
    for epoch in range(1, args.epochs + 1):
        model.train()
        tot = 0.0
        for data in tl:
            data = data.to(device); opt.zero_grad()
            out = model(data); loss = loss_fn(out, data)
            loss.backward(); opt.step(); tot += float(loss)
        # cheap val AUROC for early stop
        vs, vy = _scores(model, vl, device)
        va_auc = auroc(vs, vy) if len(set(vy.tolist())) > 1 else 0.5
        if va_auc > best_val:
            best_val, best_state, patience = va_auc, {k: v.cpu().clone()
                                                      for k, v in model.state_dict().items()}, 0
        else:
            patience += 1
        if epoch % 10 == 0 or epoch == args.epochs:
            log.info(f"    [{split} seed{seed}] epoch {epoch}/{args.epochs} "
                     f"loss={tot/max(1,len(tl)):.4f} val_auroc={va_auc:.3f} best={best_val:.3f}")
        if patience >= args.patience:
            log.info(f"    early stop at epoch {epoch}"); break

    if best_state:
        model.load_state_dict(best_state)
    ensure(CHECKPOINTS / "gat")
    import torch as _t
    _t.save(model.state_dict(), CHECKPOINTS / "gat" / f"{split}_seed{seed}.pt")

    # ---- evaluate
    tr_s, tr_y = _scores(model, tl, device)
    thr = _youden(tr_s, tr_y)
    te_s, te_y, te_types, te_loc = _scores(model, el, device, want_extra=True)
    pred = (te_s >= thr).astype(int)
    m = {"auroc": round(auroc(te_s, te_y), 3), **threshold_metrics(te_y, pred),
         "n_test": int(len(te_y))}
    return m


def _scores(model, loader, device, want_extra=False):
    import torch
    model.eval()
    S, Y, T, L = [], [], [], []
    with torch.no_grad():
        for data in loader:
            data = data.to(device)
            out = model(data)
            S.append(torch.sigmoid(out["det"]).cpu().numpy())
            Y.append(data.y.cpu().numpy())
            if want_extra:
                T.append(out["typ"].argmax(1).cpu().numpy())
                L.append(torch.sigmoid(out["loc"]).cpu().numpy())
    S = np.concatenate(S) if S else np.array([])
    Y = np.concatenate(Y) if Y else np.array([])
    if want_extra:
        return S, Y, (np.concatenate(T) if T else np.array([])), (np.concatenate(L) if L else np.array([]))
    return S, Y


def main() -> int:
    ap = argparse.ArgumentParser(description="CipherGuard Phase 5: Hybrid GAT+MLP")
    ap.add_argument("--epochs", type=int, default=150)
    ap.add_argument("--seeds", type=int, default=5)
    ap.add_argument("--batch-size", type=int, default=16)
    ap.add_argument("--hidden", type=int, default=64)
    ap.add_argument("--heads", type=int, default=4)
    ap.add_argument("--lr", type=float, default=5e-4)
    ap.add_argument("--patience", type=int, default=30)
    args = ap.parse_args()

    log = get_logger("05_train_gat")
    if not _torch_ok():
        log.warn("torch / torch_geometric NOT available on this machine.")
        log.info("This is the GPU-cluster model. To run it:")
        log.info("  pip install -r requirements-gpu.txt   (torch + torch_geometric + CUDA build)")
        log.info("  python scripts/05_train_gat.py --epochs 150 --seeds 5")
        log.info("The numpy gate/E6 results (results/gate, results/e6) stand in until then.")
        log.done("no-op on non-GPU box (staged for cluster)")
        return 0

    results = {}
    for split in STUDY_SPLITS:
        per_seed = []
        for seed in range(args.seeds):
            log.info(f"training {split} (seed {seed}) ...")
            per_seed.append(train_one(split, seed, args, log))
        # aggregate mean +/- std
        keys = ["auroc", "tpr", "fpr", "f1", "accuracy"]
        agg = {k: {"mean": round(float(np.mean([r[k] for r in per_seed])), 3),
                   "std": round(float(np.std([r[k] for r in per_seed])), 3)} for k in keys}
        results[split] = {"per_seed": per_seed, "aggregate": agg}
        log.info(f"{split}: AUROC {agg['auroc']['mean']}±{agg['auroc']['std']} "
                 f"TPR {agg['tpr']['mean']}±{agg['tpr']['std']} "
                 f"FPR {agg['fpr']['mean']}±{agg['fpr']['std']}")

    ensure(RESULTS / "gat")
    write_json(RESULTS / "gat" / "metrics.json",
               {"timestamp": datetime.now().isoformat(timespec="seconds"),
                "config": vars(args), "results": results})
    ts_dir = ensure(REPORTS / "gat" / datetime.now().strftime("%Y%m%d_%H%M%S"))
    lines = ["# CipherGuard Phase 5 -- Hybrid GAT+MLP", "",
             f"seeds={args.seeds} epochs={args.epochs}", "",
             "| split | AUROC | TPR | FPR |", "|---|---|---|---|"]
    for s, r in results.items():
        a = r["aggregate"]
        lines.append(f"| {s} | {a['auroc']['mean']}±{a['auroc']['std']} | "
                     f"{a['tpr']['mean']}±{a['tpr']['std']} | {a['fpr']['mean']}±{a['fpr']['std']} |")
    (ts_dir / "report.md").write_text("\n".join(lines))
    log.info(f"metrics -> {RESULTS/'gat'/'metrics.json'}")
    log.done("GAT training complete")
    return 0


if __name__ == "__main__":
    sys.exit(main())
