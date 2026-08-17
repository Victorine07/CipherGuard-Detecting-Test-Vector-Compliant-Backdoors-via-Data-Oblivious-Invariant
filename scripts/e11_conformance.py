#!/usr/bin/env python3
"""e11_conformance.py -- Gate 2: conformance of real third-party implementations.

Differential-tests each vendored third-party implementation (thirdparty/MANIFEST.json) against
our HOL-verified reference for the same cipher. First validates that the verified reference itself
reproduces the official published test vectors (fails loudly otherwise, since a wrong oracle would
invalidate every downstream verdict). Then, per implementation, reports official-vector reproduction
and random-input agreement with the reference, and classifies it CONFORMING / NON-CONFORMING / ERROR.

Cluster-safe: PROJECT_ROOT-relative paths, no Isabelle, no network (third-party files are vendored).
Checkpoint-logged so a failure can be pinpointed from a log tail.

Usage: python scripts/e11_conformance.py [--n-random N] [--limit K] [--manifest PATH]
"""
from __future__ import annotations
import argparse
import sys
import time
from datetime import datetime
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))

from src.common.logging import get_logger
from src.common.io import write_json
from src.common.paths import THIRDPARTY, MODELS_DIR, REPORTS, ensure
from src.corpus.conformance import (
    load_manifest, assess, reference_official_check, REFERENCE_VECTORS,
)


def main() -> int:
    ap = argparse.ArgumentParser(description="CipherGuard Gate 2: third-party conformance sweep")
    ap.add_argument("--manifest", type=Path, default=THIRDPARTY / "MANIFEST.json")
    ap.add_argument("--thirdparty-dir", type=Path, default=THIRDPARTY)
    ap.add_argument("--models-dir", type=Path, default=MODELS_DIR)
    ap.add_argument("--n-random", type=int, default=1000,
                    help="random plaintext/key pairs per variant (default 1000)")
    ap.add_argument("--limit", type=int, default=None, help="assess only the first K implementations")
    args = ap.parse_args()

    log = get_logger("e11_conformance")
    t0 = time.time()
    log.info(f"manifest={args.manifest}")
    log.info(f"thirdparty_dir={args.thirdparty_dir}  models_dir={args.models_dir}  n_random={args.n_random}")

    if not args.manifest.exists():
        raise log.fail(f"manifest not found: {args.manifest}")
    manifest = load_manifest(args.manifest)
    impls = manifest.get("implementations", [])
    if args.limit:
        impls = impls[: args.limit]
    if not impls:
        raise log.fail("manifest lists no implementations")
    n = len(impls)
    total_steps = n + 2

    # CKPT 1: validate the oracle itself against official published vectors -- fail loudly.
    log.ckpt("validating verified reference against official published test vectors", 1, total_steps)
    oracle_checks = {}
    for stem in REFERENCE_VECTORS:
        passed, tot = reference_official_check(stem, args.models_dir)
        oracle_checks[stem] = [passed, tot]
        if passed != tot:
            raise log.fail(f"verified reference '{stem}' fails official vectors ({passed}/{tot}); "
                           f"oracle is not trustworthy, aborting")
        log.info(f"  reference {stem}: official vectors {passed}/{tot} OK")

    # CKPT 2..n+1: assess each implementation.
    results = []
    for i, entry in enumerate(impls, 1):
        log.ckpt(f"assessing {entry['label']} ({entry['cipher']}, "
                 f"{len(entry['variants'])} variant(s)) from {entry['file']}", i + 1, total_steps)
        res = assess(entry, models_dir=args.models_dir,
                     thirdparty_dir=args.thirdparty_dir, n_random=args.n_random)
        off = sum(v["official_pass"] for v in res["variants"])
        off_n = sum(v["official_total"] for v in res["variants"])
        rnd = sum(v["random_agree"] for v in res["variants"])
        rnd_n = sum(v["random_total"] for v in res["variants"])
        log.info(f"  {entry['label']}: {res['verdict']}  official={off}/{off_n}  random={rnd}/{rnd_n}")
        if res["verdict"] == "NON-CONFORMING":
            fd = next((v["first_disagreement"] for v in res["variants"] if v["first_disagreement"]), None)
            log.warn(f"  {entry['label']} NON-CONFORMING (expected='{res.get('expected')}'); e.g. {fd}")
        elif res["verdict"] == "ERROR":
            log.warn(f"  {entry['label']} could not be driven by its adapter (interface error)")
        results.append(res)

    # CKPT n+2: write artifacts.
    log.ckpt("writing artifacts", total_steps, total_steps)
    conforming = [r for r in results if r["verdict"] == "CONFORMING"]
    nonconf = [r for r in results if r["verdict"] == "NON-CONFORMING"]
    errored = [r for r in results if r["verdict"] == "ERROR"]
    agree_pts = sum(v["random_agree"] for r in conforming for v in r["variants"])

    ts = datetime.now().strftime("%Y%m%d_%H%M%S")
    summary = {
        "timestamp": datetime.now().isoformat(timespec="seconds"),
        "config": {"manifest": str(args.manifest), "thirdparty_dir": str(args.thirdparty_dir),
                   "models_dir": str(args.models_dir), "n_random": args.n_random,
                   "limit": args.limit},
        "oracle_official_checks": oracle_checks,
        "n_implementations": len(results),
        "n_conforming": len(conforming),
        "n_nonconforming": len(nonconf),
        "n_error": len(errored),
        "conforming_agreement_points": agree_pts,
        "results": results,
        "wall_clock_sec": round(time.time() - t0, 2),
    }
    outdir = ensure(REPORTS / "conformance" / ts)
    write_json(outdir / "summary.json", summary)

    log.info(f"conforming={len(conforming)}  nonconforming={len(nonconf)}  error={len(errored)}")
    log.info(f"conforming implementations agree with the reference on {agree_pts} random points")
    if nonconf:
        log.info(f"non-conforming: {[r['label'] for r in nonconf]}")
    log.info(f"summary -> {outdir / 'summary.json'}")
    log.done(f"assessed {len(results)} implementations in {summary['wall_clock_sec']}s")
    return 0


if __name__ == "__main__":
    sys.exit(main())
