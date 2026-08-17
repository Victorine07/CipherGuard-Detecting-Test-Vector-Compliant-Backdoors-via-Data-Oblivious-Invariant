#!/usr/bin/env python3
"""
02_extract.py -- CipherGuard Stage 02: structural graph + PDV extraction.

For each labeled item (datasets/items/*.json) it extracts a firewall-safe structural
graph and a PDV from the item's source (the deployable "source front"), and for
tampered items computes localization ground truth as the clean/tampered graph delta.

Outputs:
  datasets/graphs/source/<item_id>.json   graph + pdv + localization
  updates datasets/items/<item_id>.json    graph_path, pdv, node/edge counts, firewall

Cluster-safe; checkpoint-logged; fails loud on empty/malformed graphs.
Usage: python scripts/02_extract.py [--limit N] [--no-firewall]
"""
from __future__ import annotations
import argparse
import sys
from datetime import datetime
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))

from src.common.logging import get_logger
from src.common.io import read_json, write_json
from src.common.paths import REGISTRY, DATASETS, REPORTS, ensure
from src.extraction.graph import extract_graph, anonymize, NODE_DIM
from src.extraction.pdv import extract_pdv, PDV_DIM
from src.extraction.localize import localize

ITEMS_DIR = DATASETS / "items"
TAMPERED_DIR = DATASETS / "tampered"
GRAPHS_DIR = DATASETS / "graphs" / "source"


def ctx_for(variant: str, registry: Path) -> dict:
    e = read_json(registry / f"{variant}.json")
    ts = e.get("tamperable_sites", {}) or {}
    return {
        "stem": variant.lower(),
        "block_size": e.get("block_size"), "key_size": e.get("key_size"),
        "rounds": e.get("rounds"),
        "tamperable_sites": ts,
        "nonlinear_fn_names": list((ts.get("nonlinear_ops") or {}).keys()),
        "keysched_names": ts.get("key_schedule") or [],
    }


def main() -> int:
    ap = argparse.ArgumentParser(description="CipherGuard Stage 02: extraction")
    ap.add_argument("--items", type=Path, default=ITEMS_DIR)
    ap.add_argument("--registry", type=Path, default=REGISTRY)
    ap.add_argument("--limit", type=int, default=None)
    ap.add_argument("--no-firewall", action="store_true", help="keep identifiers (E4 ablation)")
    args = ap.parse_args()

    log = get_logger("02_extract")
    ensure(GRAPHS_DIR)
    firewall = not args.no_firewall
    log.info(f"items = {args.items}  registry = {args.registry}")
    log.info(f"graphs -> {GRAPHS_DIR}  firewall = {firewall}")
    log.info(f"NODE_DIM = {NODE_DIM}  PDV_DIM = {PDV_DIM}")

    item_files = sorted(args.items.glob("*.json"))
    if args.limit:
        item_files = item_files[: args.limit]
    if not item_files:
        raise log.fail(f"no items under {args.items}")
    n = len(item_files)
    log.info(f"{n} items to extract")

    ctx_cache: dict = {}
    clean_graph_cache: dict = {}     # variant -> clean graph (for localization)
    n_ok, n_localized, sizes = 0, 0, []

    for i, f in enumerate(item_files, 1):
        item = read_json(f)
        variant, item_id = item["variant"], item["item_id"]
        ctx = ctx_cache.get(variant) or ctx_cache.setdefault(variant, ctx_for(variant, args.registry))

        src_path = Path(item["source_path"])
        if not src_path.exists():
            raise log.fail(f"{item_id}: source missing at {src_path}")
        graph = extract_graph(src_path.read_text(), ctx)
        if graph["n_nodes"] == 0:
            raise log.fail(f"{item_id}: extracted an EMPTY graph")

        # clean graph for this variant (for localization diff)
        if variant not in clean_graph_cache:
            clean_src = (TAMPERED_DIR / f"{variant}__T0.py")
            if clean_src.exists():
                clean_graph_cache[variant] = extract_graph(clean_src.read_text(), ctx)

        loc = None
        if item["is_tampered"] and variant in clean_graph_cache:
            loc = localize(clean_graph_cache[variant], graph)
            if loc["n_changed"] > 0:
                n_localized += 1

        pdv, pdv_names = extract_pdv(graph, ctx)
        if firewall:
            graph = anonymize(graph)

        graph_out = {
            "item_id": item_id, "variant": variant, "is_tampered": item["is_tampered"],
            "tamper_type": item["tamper_type"], "node_dim": NODE_DIM, "pdv_dim": PDV_DIM,
            "graph": graph, "pdv": pdv, "pdv_names": pdv_names, "localization": loc,
        }
        gpath = GRAPHS_DIR / f"{item_id}.json"
        write_json(gpath, graph_out)

        item.update({"graph_path": str(gpath), "pdv": pdv,
                     "n_nodes": graph["n_nodes"], "n_edges": graph["n_edges"],
                     "firewall": firewall,
                     "localization": (loc["changed_node_ids"] if loc else None)})
        write_json(f, item)

        n_ok += 1
        sizes.append(graph["n_nodes"])
        if i % 25 == 0 or i == n:
            log.ckpt(f"{item_id} [{item['tamper_type']}] nodes={graph['n_nodes']} "
                     f"edges={graph['n_edges']} "
                     f"loc={loc['n_changed'] if loc else '-'}", i, n)

    ts_dir = ensure(REPORTS / "extract" / datetime.now().strftime("%Y%m%d_%H%M%S"))
    summary = {
        "timestamp": datetime.now().isoformat(timespec="seconds"),
        "n_items": n, "n_ok": n_ok, "firewall": firewall,
        "node_dim": NODE_DIM, "pdv_dim": PDV_DIM,
        "graph_size": {"min": min(sizes), "max": max(sizes),
                       "mean": round(sum(sizes) / len(sizes), 1)},
        "tampered_with_localization": n_localized,
    }
    write_json(ts_dir / "summary.json", summary)
    log.info(f"summary -> {ts_dir/'summary.json'}")
    log.info(f"graph sizes: {summary['graph_size']}  localized tampers: {n_localized}")
    log.done(f"extracted {n_ok}/{n} graphs to {GRAPHS_DIR}")
    return 0


if __name__ == "__main__":
    sys.exit(main())
