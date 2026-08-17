"""Graph -> fixed-length feature vector (CipherGuard Stage 04, numpy readout).

No torch on this box, so the detector consumes a graph-level readout rather than a
full GAT. The readout is scale-invariant (mean/max over node features -> fractions,
not absolute counts) plus a few STRUCTURAL MOTIF features that make explicit the
co-occurrences a message-passing GNN would otherwise learn -- most importantly the
T6 fingerprint: a branch / compare / key-tainted return INSIDE the encrypt entry
(absent from every clean cipher, whose only branches live in the key schedule).

Everything is firewall-safe (derived from structural flags, never identifiers).
The full GAT+MLP is the intended cluster model (Phase 5); this suffices to answer
the gate question: is the signal separable and does it generalize?
"""
from __future__ import annotations
from typing import Any, Dict, List

import numpy as np

from ..extraction.graph import KINDS, OPS, FLAGS

_K, _O = len(KINDS), len(OPS)
_FLAG_OFF = _K + _O


def _fi(flag: str) -> int:
    return _FLAG_OFF + FLAGS.index(flag)


def _ki(kind: str) -> int:
    return KINDS.index(kind)


I_ENC = _fi("in_encrypt_entry")
I_BRANCH = _fi("is_branch_test")
I_KEYT = _fi("key_tainted")
I_RET = _fi("is_return_value")
I_KEYSCHED = _fi("in_key_sched")
K_CMP = _ki("Compare")
K_IF = _ki("If")

MOTIF_NAMES = ["motif_branch_in_encrypt", "motif_compare_in_encrypt",
               "motif_keytaint_in_encrypt", "motif_return_in_encrypt",
               "motif_keytaint_branch_in_keysched"]


def _motifs(X: np.ndarray) -> List[float]:
    enc = X[:, I_ENC] > 0.5
    # T6 fingerprint pieces, each ~0 for clean ciphers (their branches are in key sched)
    branch_in_enc = float(np.sum(enc & (X[:, I_BRANCH] > 0.5)))
    cmp_in_enc = float(np.sum(enc & (X[:, K_CMP] > 0.5)))
    keyt_in_enc = float(np.sum(enc & (X[:, I_KEYT] > 0.5)))
    ret_in_enc = float(np.sum(enc & (X[:, I_RET] > 0.5)))
    # S6 signature: a branch INSIDE the key schedule whose test is key-value-tainted.
    # Clean schedules branch on the loop counter (not key-tainted) -> ~0.
    ks = X[:, I_KEYSCHED] > 0.5
    keyt_branch_in_ks = float(np.sum(ks & (X[:, I_BRANCH] > 0.5) & (X[:, I_KEYT] > 0.5)))
    return [np.log1p(branch_in_enc), np.log1p(cmp_in_enc), np.log1p(keyt_in_enc),
            np.log1p(ret_in_enc), np.log1p(keyt_branch_in_ks)]


def readout(graph_json: Dict[str, Any]) -> np.ndarray:
    g = graph_json["graph"]
    X = np.array([n["feat"] for n in g["nodes"]], dtype=np.float64)  # (N, 54)
    if X.size == 0:
        raise ValueError(f"{graph_json['item_id']}: empty graph")
    mean = X.mean(axis=0)
    mx = X.max(axis=0)
    motifs = np.array(_motifs(X), dtype=np.float64)
    pdv = np.array(graph_json["pdv"], dtype=np.float64)
    return np.concatenate([mean, mx, motifs, pdv])


def feature_names(graph_json: Dict[str, Any]) -> List[str]:
    base = KINDS + OPS + FLAGS + ["const_mag", "subtree_size"]
    return ([f"mean_{n}" for n in base] + [f"max_{n}" for n in base]
            + MOTIF_NAMES + [f"pdv_{i}" for i in range(len(graph_json["pdv"]))])
