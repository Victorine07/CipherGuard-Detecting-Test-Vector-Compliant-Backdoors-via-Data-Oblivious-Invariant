#!/usr/bin/env python3
"""
e6_backdoor_styles.py -- CipherGuard robustness study: diverse backdoor styles.

Answers the make-or-break question behind the reviewers' "easy to fool / did it
memorize one pattern?" concern. We inject FOUR structurally-distinct backdoor
styles (src/tamper/backdoor_styles.py), verify each preserves the test vector AND
is exploitable, then run two analyses on cipher-disjoint cohorts:

  (1) ONE-CLASS per style   -- fit on CLEAN only (never sees any backdoor); which
                               styles show up as structural anomalies?
  (2) SUPERVISED leave-one-style-out -- train on clean + 3 styles, test detection on
                               the HELD-OUT style; does supervised transfer across styles?

High held-out-style detection => the detector learned "backdoor-ness", not one
pattern. Low => an honest brittleness boundary, found before review not after.

Usage: python scripts/e6_backdoor_styles.py [--limit N] [--seed N]
"""
from __future__ import annotations
import argparse
import random
import sys
from datetime import datetime
from pathlib import Path

import numpy as np

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))

from src.common.logging import get_logger
from src.common.io import read_json, write_json
from src.common.paths import REGISTRY, MODELS_DIR, RESULTS, REPORTS, ensure
from src.common.seed import set_seed
from src.extraction.graph import extract_graph
from src.extraction.pdv import extract_pdv
from src.models.readout import readout
from src.models.detector import Standardizer, LogisticDetector, OneClassDetector
from src.models.metrics import auroc, threshold_metrics
from src.tamper.backdoor_styles import STYLES, BENCHMARK_STYLES
from src.tamper.oracle import evaluate, _exec_module, _find

STYLE_IDS = BENCHMARK_STYLES      # S1..S6 (learned per-style study on the benchmark)


def ctx_for(entry: dict) -> dict:
    ts = entry.get("tamperable_sites", {}) or {}
    return {"stem": entry["variant"].lower(), "block_size": entry["block_size"],
            "key_size": entry["key_size"], "rounds": entry["rounds"],
            "tamperable_sites": ts,
            "nonlinear_fn_names": list((ts.get("nonlinear_ops") or {}).keys()),
            "keysched_names": ts.get("key_schedule") or []}


def featurize(source: str, ctx: dict) -> np.ndarray:
    g = extract_graph(source, ctx)
    pdv, _ = extract_pdv(g, ctx)
    return readout({"item_id": ctx["stem"], "graph": g, "pdv": pdv})


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


def main() -> int:
    ap = argparse.ArgumentParser(description="CipherGuard E6: backdoor-style robustness")
    ap.add_argument("--registry", type=Path, default=REGISTRY)
    ap.add_argument("--models-dir", type=Path, default=MODELS_DIR)
    ap.add_argument("--limit", type=int, default=None)
    ap.add_argument("--seed", type=int, default=20260730)
    args = ap.parse_args()
    set_seed(args.seed)

    log = get_logger("e6_styles")
    reg_files = sorted(args.registry.glob("*.json"))
    if args.limit:
        reg_files = reg_files[: args.limit]
    log.info(f"{len(reg_files)} registry variants; models = {args.models_dir}")

    # ---- inject + verify + featurize
    rows = []                      # {cipher, family, style, feat, label}
    validity = {s: 0 for s in STYLE_IDS}
    ciphers_ok = []
    for i, rf in enumerate(reg_files, 1):
        e = read_json(rf); variant = e["variant"]; stem = variant.lower()
        model = args.models_dir / f"{stem}.py"
        if not model.exists() or not e["block_size"] or not e["key_size"]:
            continue
        ctx = ctx_for(e)
        clean_src = model.read_text()
        block, key = e["block_size"], e["key_size"]
        try:
            clean_feat = featurize(clean_src, ctx)
        except Exception as ex:
            log.warn(f"{variant}: clean featurize failed ({ex}) -> skip"); continue

        style_feats = {}
        rng = random.Random(args.seed + (hash(variant) % 10000))
        for sid in STYLE_IDS:
            st = STYLES[sid]
            try:
                tsrc, meta = st.inject(clean_src, ctx, rng)
                if tsrc is None:
                    continue
                orc = evaluate(clean_src, tsrc, stem, block, key)
                if not orc.get("ok") or not orc.get("passes_test_vector"):
                    continue                             # KAT broken -> not a valid backdoor
                cln_ns = _exec_module(clean_src, f"{stem}_c")
                bd_ns = _exec_module(tsrc, f"{stem}_b")
                enc_c, enc_bd = _find(cln_ns, stem, "encrypt"), _find(bd_ns, stem, "encrypt")
                if enc_c is None or enc_bd is None:
                    continue
                if not st.exploit(enc_c, enc_bd, block, key, meta, random.Random(args.seed + 7)):
                    continue                             # not actually exploitable
                style_feats[sid] = featurize(tsrc, ctx)
                validity[sid] += 1
            except Exception:
                continue

        if not style_feats:
            continue
        ciphers_ok.append(variant)
        rows.append({"cipher": variant, "family": e["family"], "style": "clean",
                     "feat": clean_feat, "label": 0})
        for sid, ft in style_feats.items():
            rows.append({"cipher": variant, "family": e["family"], "style": sid,
                         "feat": ft, "label": 1})
        if i % 10 == 0 or i == len(reg_files):
            log.ckpt(f"{variant}: styles valid={sorted(style_feats)}", i, len(reg_files))

    log.info(f"ciphers with >=1 valid backdoor style: {len(ciphers_ok)}")
    log.info(f"per-style validity (ciphers injected+verified): {validity}")
    if len(ciphers_ok) < 6:
        raise log.fail("too few ciphers with valid backdoors to run the study")

    # ---- cipher-disjoint cohorts
    rng = random.Random(args.seed)
    cohort = ciphers_ok[:]; rng.shuffle(cohort)
    cut = int(0.70 * len(cohort))
    train_c, test_c = set(cohort[:cut]), set(cohort[cut:])

    def feats(pred):
        r = [x for x in rows if pred(x)]
        return np.array([x["feat"] for x in r]), np.array([x["label"] for x in r]), r

    # ---- (1) one-class per style
    Xtr_clean, _, _ = feats(lambda x: x["cipher"] in train_c and x["style"] == "clean")
    std = Standardizer().fit(Xtr_clean)
    oc = OneClassDetector(quantile=0.99).fit(std.transform(Xtr_clean))
    Xte_clean, _, _ = feats(lambda x: x["cipher"] in test_c and x["style"] == "clean")
    clean_fpr = float(np.mean(oc.predict(std.transform(Xte_clean)))) if len(Xte_clean) else float("nan")
    oneclass = {"clean_FPR": round(clean_fpr, 3), "n_clean_test": len(Xte_clean), "per_style": {}}
    for sid in STYLE_IDS:
        Xs, _, rs = feats(lambda x: x["cipher"] in test_c and x["style"] == sid)
        if len(Xs) == 0:
            oneclass["per_style"][sid] = {"n": 0}; continue
        pred = oc.predict(std.transform(Xs))
        # AUROC vs clean test
        sc = oc.score(std.transform(np.vstack([Xs, Xte_clean])))
        yy = np.array([1] * len(Xs) + [0] * len(Xte_clean))
        oneclass["per_style"][sid] = {"n": len(Xs), "TPR": round(float(np.mean(pred)), 3),
                                      "auroc": round(auroc(sc, yy), 3)}

    # ---- (2) supervised leave-one-style-out
    loso = {}
    for held in STYLE_IDS:
        Xtr, ytr, _ = feats(lambda x: x["cipher"] in train_c and x["style"] != held)
        Xte, yte, rte = feats(lambda x: x["cipher"] in test_c
                              and (x["style"] == "clean" or x["style"] == held))
        held_n = sum(1 for r in rte if r["style"] == held)
        if held_n == 0 or Xtr.size == 0:
            loso[held] = {"n_held": held_n, "note": "insufficient"}; continue
        s = Standardizer().fit(Xtr)
        clf = LogisticDetector(seed=args.seed).fit(s.transform(Xtr), ytr)
        thr = _youden(clf.score(s.transform(Xtr)), ytr)
        sc = clf.score(s.transform(Xte))
        pred = (sc >= thr).astype(int)
        m = threshold_metrics(yte, pred)
        held_tpr = round(float(np.mean([pred[i] for i, r in enumerate(rte) if r["style"] == held])), 3)
        loso[held] = {"n_held": held_n, "held_TPR": held_tpr, "clean_FPR": m["fpr"],
                      "auroc": round(auroc(sc, yte), 3)}

    # ---- verdict
    oc_leak = [oneclass["per_style"][s].get("TPR", 0) for s in ("S1", "S2", "S3")
               if oneclass["per_style"][s].get("n", 0) > 0]
    loso_held = [loso[s].get("held_TPR", 0) for s in STYLE_IDS if "held_TPR" in loso[s]]
    verdict = {
        "oneclass_leak_styles_min_TPR": round(min(oc_leak), 3) if oc_leak else None,
        "oneclass_S4_TPR": oneclass["per_style"].get("S4", {}).get("TPR"),
        "loso_min_held_TPR": round(min(loso_held), 3) if loso_held else None,
        "reading": ("robust: detection transfers to held-out styles"
                    if (loso_held and min(loso_held) >= 0.6) else
                    "partial/brittle: some styles do not transfer -- honest boundary"),
    }

    out = {"timestamp": datetime.now().isoformat(timespec="seconds"), "seed": args.seed,
           "n_ciphers": len(ciphers_ok), "train_ciphers": len(train_c), "test_ciphers": len(test_c),
           "style_validity": validity, "oneclass": oneclass, "loso_supervised": loso,
           "verdict": verdict}
    ensure(RESULTS / "e6")
    write_json(RESULTS / "e6" / "metrics.json", out)

    # ---- report + logs
    log.info(f"cohorts: train={len(train_c)} test={len(test_c)} ciphers")
    log.info(f"one-class clean FPR={oneclass['clean_FPR']}  per-style:")
    for s in STYLE_IDS:
        ps = oneclass["per_style"][s]
        log.info(f"   {s} [{STYLES[s].name}]: n={ps.get('n')} TPR={ps.get('TPR')} auroc={ps.get('auroc')}")
    log.info("supervised leave-one-style-out (held-out style detection):")
    for s in STYLE_IDS:
        d = loso[s]
        log.info(f"   held={s}: held_TPR={d.get('held_TPR')} clean_FPR={d.get('clean_FPR')} "
                 f"auroc={d.get('auroc')} (n={d.get('n_held')})")
    log.info(f"VERDICT: {verdict['reading']}")

    ts_dir = ensure(REPORTS / "e6" / datetime.now().strftime("%Y%m%d_%H%M%S"))
    _report(ts_dir / "report.md", out)
    log.info(f"metrics -> {RESULTS/'e6'/'metrics.json'}")
    log.info(f"report  -> {ts_dir/'report.md'}")
    log.done("backdoor-style robustness study complete")
    return 0


def _report(path: Path, o: dict) -> None:
    L = ["# CipherGuard E6 -- backdoor-style robustness", "",
         f"Ciphers with >=1 valid backdoor: {o['n_ciphers']} "
         f"(train {o['train_ciphers']} / test {o['test_ciphers']}, cipher-disjoint).",
         f"Per-style validity (KAT-preserving + exploitable): {o['style_validity']}", "",
         "## Styles", ""]
    for s in STYLE_IDS:
        L.append(f"- **{s}** — {STYLES[s].name}")
    L += ["", "## (1) One-class (trained on CLEAN only) — which styles are anomalous?",
          f"- clean FPR = {o['oneclass']['clean_FPR']} (on {o['oneclass']['n_clean_test']} held-out clean)",
          "", "| style | n | TPR | AUROC |", "|---|---|---|---|"]
    for s in STYLE_IDS:
        ps = o["oneclass"]["per_style"][s]
        L.append(f"| {s} | {ps.get('n')} | {ps.get('TPR')} | {ps.get('auroc')} |")
    L += ["", "## (2) Supervised leave-one-style-out — does detection transfer to an unseen style?",
          "| held-out style | n | held TPR | clean FPR | AUROC |", "|---|---|---|---|---|"]
    for s in STYLE_IDS:
        d = o["loso_supervised"][s]
        L.append(f"| {s} | {d.get('n_held')} | {d.get('held_TPR')} | {d.get('clean_FPR')} | {d.get('auroc')} |")
    L += ["", f"**Verdict:** {o['verdict']['reading']}",
          f"(one-class leak-style min TPR = {o['verdict']['oneclass_leak_styles_min_TPR']}, "
          f"S4 TPR = {o['verdict']['oneclass_S4_TPR']}, "
          f"LOSO min held TPR = {o['verdict']['loso_min_held_TPR']})"]
    path.write_text("\n".join(L))


if __name__ == "__main__":
    sys.exit(main())
