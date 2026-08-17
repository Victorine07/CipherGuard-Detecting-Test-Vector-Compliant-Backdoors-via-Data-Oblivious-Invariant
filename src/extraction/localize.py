"""Localization ground truth via clean/tampered graph diff (CipherGuard Stage 02).

Because a tamper is a small local edit, the injected change is exactly the delta
between the clean and tampered graphs. Using subtree hashes (robust to index
shifts from inserted statements), the tampered nodes whose subtree hash is absent
from the clean graph's hash multiset ARE the tamper. This yields objective
node-level localization labels for the E8 localization experiment -- no manual
annotation, no reliance on identifier names.
"""
from __future__ import annotations
from collections import Counter
from typing import Any, Dict, List


def localize(clean_graph: Dict[str, Any], tampered_graph: Dict[str, Any]) -> Dict[str, Any]:
    clean_hashes = Counter(nd["hash"] for nd in clean_graph["nodes"])
    changed: List[int] = []
    remaining = Counter(clean_hashes)
    for nd in tampered_graph["nodes"]:
        h = nd["hash"]
        if remaining.get(h, 0) > 0:
            remaining[h] -= 1
        else:
            changed.append(nd["id"])
    return {
        "changed_node_ids": changed,
        "n_changed": len(changed),
        "n_clean_nodes": len(clean_graph["nodes"]),
        "n_tampered_nodes": len(tampered_graph["nodes"]),
        "delta_nodes": len(tampered_graph["nodes"]) - len(clean_graph["nodes"]),
    }
