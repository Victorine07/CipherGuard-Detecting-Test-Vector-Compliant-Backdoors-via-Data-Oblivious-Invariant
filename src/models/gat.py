"""Hybrid GAT + MLP detector.
 Design follows:

  * GAT branch  : GATConv layers over the firewall-safe structural graph (54-dim
                  node features, `src/extraction/graph.py`) -> mean+max readout.
  * MLP branch  : dense over the 26-dim PDV.
  * fusion      : concat -> heads: detection (binary), tamper-type (7-way), and a
                  per-node localization head trained against the graph-delta labels.

Everything stays firewall-safe (no identifiers). Import guarded so `py_compile` and
the CPU boxes don't choke; scripts/05_train_gat.py checks torch before importing.
"""
from __future__ import annotations
from pathlib import Path
from typing import List

import torch
import torch.nn as nn
import torch.nn.functional as F
from torch_geometric.data import Data, Dataset
from torch_geometric.loader import DataLoader
from torch_geometric.nn import GATConv, global_max_pool, global_mean_pool

from ..common.io import read_json

TAMPER_TYPES = ["T0", "T1", "T2", "T3", "T4", "T5", "T6"]
TYPE_IDX = {t: i for i, t in enumerate(TAMPER_TYPES)}


# --------------------------------------------------------------------------- dataset
class CipherGraphDataset(Dataset):
    """Builds PyG `Data` objects from datasets/graphs/source/<item_id>.json,
    restricted to the item_ids in a given split fold."""
    def __init__(self, graphs_dir: Path, item_ids: List[str]):
        super().__init__()
        self.paths = [graphs_dir / f"{iid}.json" for iid in item_ids]
        self.paths = [p for p in self.paths if p.exists()]

    def len(self) -> int:
        return len(self.paths)

    def get(self, idx: int) -> Data:
        gj = read_json(self.paths[idx])
        g = gj["graph"]
        x = torch.tensor([n["feat"] for n in g["nodes"]], dtype=torch.float)
        if g["edges"]:
            ei = torch.tensor([[e["s"], e["t"]] for e in g["edges"]], dtype=torch.long).t().contiguous()
        else:
            ei = torch.empty((2, 0), dtype=torch.long)
        pdv = torch.tensor(gj["pdv"], dtype=torch.float).unsqueeze(0)
        y = torch.tensor([gj["is_tampered"]], dtype=torch.float)
        ytype = torch.tensor([TYPE_IDX.get(gj["tamper_type"], 0)], dtype=torch.long)
        # per-node localization target (graph-delta ids); zeros for clean
        loc = torch.zeros(x.size(0), dtype=torch.float)
        locobj = gj.get("localization")
        if locobj and locobj.get("changed_node_ids"):
            ids = [i for i in locobj["changed_node_ids"] if 0 <= i < x.size(0)]
            loc[ids] = 1.0
        d = Data(x=x, edge_index=ei, y=y, y_type=ytype, pdv=pdv, loc=loc)
        return d


# --------------------------------------------------------------------------- model
class HybridGAT(nn.Module):
    def __init__(self, node_dim: int, pdv_dim: int, hidden: int = 64, heads: int = 4,
                 n_types: int = 7, dropout: float = 0.3):
        super().__init__()
        self.g1 = GATConv(node_dim, hidden, heads=heads, dropout=dropout)
        self.g2 = GATConv(hidden * heads, hidden, heads=1, dropout=dropout)
        self.pdv = nn.Sequential(nn.Linear(pdv_dim, hidden), nn.ReLU(),
                                 nn.Linear(hidden, hidden))
        fused = hidden * 2 + hidden          # mean+max graph readout + pdv embedding
        self.det = nn.Sequential(nn.Linear(fused, hidden), nn.ReLU(),
                                 nn.Dropout(dropout), nn.Linear(hidden, 1))
        self.typ = nn.Linear(fused, n_types)
        self.loc = nn.Linear(hidden, 1)      # per-node localization from node embeddings

    def forward(self, data):
        x, ei, batch = data.x, data.edge_index, data.batch
        h = F.elu(self.g1(x, ei))
        h = F.elu(self.g2(h, ei))            # node embeddings (N, hidden)
        gemb = torch.cat([global_mean_pool(h, batch), global_max_pool(h, batch)], dim=1)
        pemb = self.pdv(data.pdv)
        fused = torch.cat([gemb, pemb], dim=1)
        return {"det": self.det(fused).squeeze(-1),
                "typ": self.typ(fused),
                "loc": self.loc(h).squeeze(-1),
                "node_batch": batch}


def loss_fn(out, data, w_type: float = 0.5, w_loc: float = 0.5) -> torch.Tensor:
    det = F.binary_cross_entropy_with_logits(out["det"], data.y)
    typ = F.cross_entropy(out["typ"], data.y_type)
    # localization only where the graph is tampered (loc has 1s); mask clean graphs
    tampered_nodes = data.y[out["node_batch"]] > 0.5
    if tampered_nodes.any():
        loc = F.binary_cross_entropy_with_logits(out["loc"][tampered_nodes],
                                                 data.loc[tampered_nodes])
    else:
        loc = torch.tensor(0.0, device=det.device)
    return det + w_type * typ + w_loc * loc


def make_loader(dataset, batch_size: int, shuffle: bool):
    return DataLoader(dataset, batch_size=batch_size, shuffle=shuffle)
