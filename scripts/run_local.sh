#!/bin/bash
# CipherGuard stage 05 — run ANYWHERE (laptop / login node / CPU), no SLURM, no GPU.
# The dataset is tiny; this finishes in minutes on CPU.
#
# Prereqs: Python 3.10-3.12 with numpy + torch (CPU build) + torch_geometric
#          (see requirements-train.txt).
set -euo pipefail

PROJECT_ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$PROJECT_ROOT"

python -c "import torch, torch_geometric; print('[run_local] torch', torch.__version__, \
'| cuda', torch.cuda.is_available(), '| pyg', torch_geometric.__version__)"

# Rebuild the dataset only if it is missing (no GPU needed for 00-03).
if [ ! -d datasets/graphs/source ] || [ -z "$(ls -A datasets/graphs/source 2>/dev/null)" ]; then
  echo "[run_local] datasets/graphs missing -> rebuilding (stages 00-03)"
  python scripts/00_corpus.py
  python scripts/01_inject.py
  python scripts/02_extract.py
  python scripts/03_dataset.py
fi

# Train + evaluate the GAT (CPU is fine). Fewer seeds by default for a quick pass.
python scripts/05_train_gat.py --epochs 150 --seeds "${1:-5}"
echo "[run_local] done -> results/gat/metrics.json"
