"""Protocol Design Vector: fixed-length high-level structural summary of a cipher.

Firewall-safe (structural statistics only, no identifiers, no security score).
Complements the fine-grained graph with architecture-level context the MLP branch
consumes (per the hybrid GAT+MLP design).
"""
from __future__ import annotations
from typing import Any, Dict, List, Tuple

_OPS = ["BitXor", "BitAnd", "BitOr", "Add", "Sub", "Mult", "Mod", "LShift", "RShift"]
_KINDS = ["Call", "If", "Compare", "Constant", "BinOp", "Subscript"]
_FLAG_IDX = {"in_round_fn": 3 + 21 + 3, "in_key_sched": 3 + 21 + 4,
             "key_tainted": 3 + 21 + 5, "is_branch_test": 3 + 21 + 7}

PDV_NAMES = (["block_norm", "key_norm", "rounds_norm", "n_nodes_norm", "n_edges_norm",
              "n_functions_norm"]
             + [f"op_frac_{o}" for o in _OPS]
             + [f"kind_frac_{k}" for k in _KINDS]
             + ["frac_round_fn", "frac_key_sched", "frac_key_tainted", "frac_branch_test",
                "has_sbox"])
PDV_DIM = len(PDV_NAMES)


def extract_pdv(graph: Dict[str, Any], ctx: Dict[str, Any]) -> Tuple[List[float], List[str]]:
    nodes = graph["nodes"]
    n = max(1, len(nodes))
    block = (ctx.get("block_size") or 0) / 128.0
    key = (ctx.get("key_size") or 0) / 256.0
    rounds = (ctx.get("rounds") or 0) / 128.0
    n_funcs = sum(1 for x in nodes if x["k"] == "FunctionDef")

    op_frac = [sum(1 for x in nodes if x["op"] == o) / n for o in _OPS]
    kind_frac = [sum(1 for x in nodes if x["k"] == k) / n for k in _KINDS]

    # flags live in the node feature vector; read via known offsets
    def flag_frac(name: str) -> float:
        idx = _FLAG_IDX[name]
        return sum(1 for x in nodes if x["feat"][idx] > 0.5) / n

    has_sbox = 1.0 if (ctx.get("tamperable_sites", {}) or {}).get("sbox") else 0.0

    vec = ([block, key, rounds, min(1.0, len(nodes) / 2000.0),
            min(1.0, graph["n_edges"] / 2000.0), min(1.0, n_funcs / 50.0)]
           + op_frac + kind_frac
           + [flag_frac("in_round_fn"), flag_frac("in_key_sched"),
              flag_frac("key_tainted"), flag_frac("is_branch_test"), has_sbox])
    assert len(vec) == PDV_DIM, f"PDV dim mismatch {len(vec)} != {PDV_DIM}"
    return vec, PDV_NAMES
