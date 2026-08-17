#!/bin/bash
# CipherGuard -- reproduce all interpretable-check experiments (the paper's headline numbers).
#
# numpy-only: no GPU, no torch, no Isabelle, no internet. Third-party implementations for the
# conformance study (e11) are vendored under thirdparty/, so it runs fully offline. The learned
# GAT baseline (stage 05) is the ONLY torch-dependent part and is intentionally left out here;
# run scripts/run_local.sh for it.
#
# Each stage derives its paths from the repo root, logs [CipherGuard][<stage>][CKPT k/N] progress
# to console + logs/, fails loudly on integrity errors, and writes machine-readable artifacts
# under results/ and reports/.
set -euo pipefail

PROJECT_ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$PROJECT_ROOT"
echo "[run_experiments] repo=$PROJECT_ROOT  python=$(python3 --version 2>&1)"

# --- build the dataset (idempotent; rebuilds only if missing) ---
if [ ! -d datasets/graphs/source ] || [ -z "$(ls -A datasets/graphs/source 2>/dev/null)" ]; then
  echo "[run_experiments] building dataset (stages 00-03)"
  python3 scripts/00_corpus.py
  python3 scripts/01_inject.py
  python3 scripts/02_extract.py
  python3 scripts/03_dataset.py
fi

# --- core detection experiments (map to the paper's research questions) ---
python3 scripts/e9_behavioral_baselines.py     # RQ1  vs fuzzing / avalanche (rare-trigger backdoors)
python3 scripts/e6_backdoor_styles.py          # RQ2  per-style robustness
python3 scripts/e10_harder_backdoors.py        # RQ2  helper-hidden adaptive backdoors (S7/S8)
python3 scripts/e13_adaptive_evasion.py        # RQ2  adaptive evasions A1/A3 + hardening (before/after)
python3 scripts/e7_graphedit_baseline.py       # RQ3  "why not diff a reference?" (Regime A vs B)
python3 scripts/e8_ct_vs_cipherguard.py        # RQ5  vs a constant-time analyzer (branchless leak)
python3 scripts/e12_property_probes.py         # RQ6  L2 property probes (weakenings) + clean FPR
python3 scripts/e14_literature_weakenings.py   # RQ6  L2 vs literature weak S-boxes (non-circular)
python3 scripts/e11_conformance.py             # RQ7  conformance vs real third-party implementations

echo "[run_experiments] DONE -- see results/, reports/, logs/ for artifacts"
echo "[run_experiments] (optional) learned GAT baseline (RQ4): bash scripts/run_local.sh"
