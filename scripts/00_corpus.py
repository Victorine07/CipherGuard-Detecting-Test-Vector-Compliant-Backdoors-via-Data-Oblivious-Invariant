#!/usr/bin/env python3
"""
00_corpus.py -- CipherGuard Stage 00: corpus verification & tamperable-site registry.

Turns new-dataset-thy-ciphers/*.thy into datasets/registry/<variant>.json, each
listing the sites the tamper engine (Stage 01) will edit, plus a literature-grounded
safe-round margin and a (behavioral, until an Isabelle node runs) verification result.

Cluster-safe: PROJECT_ROOT from __file__, pathlib, no network, no Isabelle required.
See PIPELINE.md (Stage 00) and DATASET.md (registry schema).

Usage:
    python scripts/00_corpus.py [--limit N] [--no-verify]
                                [--corpus-dir DIR] [--models-dir DIR] [--out DIR]
"""
from __future__ import annotations
import argparse
import sys
from datetime import datetime
from pathlib import Path

# make `src` importable regardless of CWD
sys.path.insert(0, str(Path(__file__).resolve().parents[1]))

from src.common.logging import get_logger
from src.common.paths import CORPUS_DIR, REGISTRY, REPORTS, MODELS_DIR, ensure
from src.common.io import write_json
from src.corpus.thy_parser import parse_theory
from src.corpus.verify import verify_variant


def list_theories(corpus_dir: Path):
    """Real variant theories only: skip editor backups (*~), templates, and ROOT."""
    out = []
    for p in sorted(corpus_dir.glob("*.thy")):
        if p.name.endswith("~") or "template" in p.name.lower() or "-v" in p.name.lower():
            continue
        out.append(p)
    return out


def main() -> int:
    ap = argparse.ArgumentParser(description="CipherGuard Stage 00: corpus registry")
    ap.add_argument("--corpus-dir", type=Path, default=CORPUS_DIR)
    ap.add_argument("--out", type=Path, default=REGISTRY)
    ap.add_argument("--models-dir", type=Path, default=MODELS_DIR)
    ap.add_argument("--limit", type=int, default=None)
    ap.add_argument("--no-verify", action="store_true", help="skip behavioral verification")
    args = ap.parse_args()

    log = get_logger("00_corpus")
    log.info(f"corpus-dir = {args.corpus_dir}")
    log.info(f"models-dir = {args.models_dir}")
    log.info(f"registry   = {ensure(args.out)}")

    theories = list_theories(args.corpus_dir)
    if args.limit:
        theories = theories[: args.limit]
    if not theories:
        raise log.fail(f"no theory files found under {args.corpus_dir}")
    n = len(theories)
    log.info(f"found {n} theory files to process")

    ok, failures, entries = [], [], []
    for i, path in enumerate(theories, 1):
        try:
            entry = parse_theory(path)
        except Exception as e:
            log.ckpt(f"{path.name}: PARSE FAILED -> {e}", i, n)
            failures.append({"file": path.name, "error": str(e)})
            continue

        if not args.no_verify:
            entry["verified"] = verify_variant(entry["variant"], models_dir=args.models_dir)
        else:
            entry["verified"] = {"status": "skipped", "notes": "--no-verify"}

        out_path = args.out / f"{entry['variant']}.json"
        write_json(out_path, entry)
        ok.append(entry)
        entries.append(entry)

        ts = entry["tamperable_sites"]
        srm = entry.get("safe_round_margin")
        v = entry["verified"]
        log.ckpt(
            f"{entry['variant']} [{entry['family']}] b{entry['block_size']}/k{entry['key_size']} "
            f"r={entry['rounds']} | rot={len(ts['rotation_amounts'])} "
            f"const={len(ts['constants'])} sbox={'Y' if ts['sbox'] else 'N'} "
            f"ks={len(ts['key_schedule'])} tv={entry['test_vectors']['count']} "
            f"| margin={'Y' if srm else 'TODO'} "
            f"| verify={v['status']}(inv={v.get('invertibility')},tv={v.get('test_vector')})",
            i, n)

    # ---------------- summary report
    fam_counts, verify_counts, no_margin = {}, {}, []
    for e in ok:
        fam_counts[e["family"]] = fam_counts.get(e["family"], 0) + 1
        st = e["verified"]["status"]
        verify_counts[st] = verify_counts.get(st, 0) + 1
        if not e.get("safe_round_margin"):
            no_margin.append(e["variant"])

    ts_dir = ensure(REPORTS / "corpus" / datetime.now().strftime("%Y%m%d_%H%M%S"))
    summary = {
        "timestamp": datetime.now().isoformat(timespec="seconds"),
        "corpus_dir": str(args.corpus_dir),
        "n_theories": n, "n_ok": len(ok), "n_failed": len(failures),
        "families": fam_counts, "verification": verify_counts,
        "variants_without_literature_margin (T1 TODO)": no_margin,
        "failures": failures,
        "variants": [
            {"variant": e["variant"], "family": e["family"],
             "block": e["block_size"], "key": e["key_size"], "rounds": e["rounds"],
             "verify": e["verified"]["status"],
             "n_rotations": len(e["tamperable_sites"]["rotation_amounts"]),
             "has_sbox": bool(e["tamperable_sites"]["sbox"]),
             "test_vectors": e["test_vectors"]["count"]}
            for e in ok],
    }
    write_json(ts_dir / "summary.json", summary)
    log.info(f"summary -> {ts_dir/'summary.json'}")
    log.info(f"families: {fam_counts}")
    log.info(f"verification: {verify_counts}")
    if no_margin:
        log.warn(f"{len(no_margin)} variants lack a literature round-margin (T1 needs manual "
                 f"grounding later): {', '.join(no_margin[:12])}{' ...' if len(no_margin)>12 else ''}")

    if failures:
        log.error(f"{len(failures)} theory file(s) failed to parse:")
        for f in failures:
            log.error(f"  - {f['file']}: {f['error']}")
        log.done(f"registry written for {len(ok)}/{n} (WITH {len(failures)} FAILURES)")
        return 1
    log.done(f"registry written for {len(ok)}/{n} variants")
    return 0


if __name__ == "__main__":
    sys.exit(main())
