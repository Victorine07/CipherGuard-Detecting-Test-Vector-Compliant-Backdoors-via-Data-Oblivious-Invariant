#!/bin/bash
#SBATCH --job-name=cipherguard-gat
#SBATCH --cpus-per-task=4
#SBATCH --mem=16G
#SBATCH --time=02:00:00
#SBATCH --output=logs/slurm/%x_%j.out
## GPU IS OPTIONAL — the dataset is tiny; CPU finishes in minutes. Uncomment ONLY
## if you scale up a lot. Also edit partition/account for your cluster.
## SBATCH --gres=gpu:1
#
# For a laptop / login node / non-SLURM CPU run, use scripts/run_local.sh instead.
# Deps: Python 3.10-3.12 + numpy + torch (CPU build fine) + torch_geometric
#       (see requirements-train.txt). Assumes stages 00-03 already produced
#       datasets/graphs + datasets/splits (they need no GPU).
set -euo pipefail

PROJECT_ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$PROJECT_ROOT"
mkdir -p logs/slurm

echo "[run_cluster] host=$(hostname) cwd=$PROJECT_ROOT"
python -c "import torch; print('[run_cluster] torch', torch.__version__, 'cuda', torch.cuda.is_available())"

# (Re)build data on the login node if needed (no GPU):
#   python scripts/00_corpus.py && python scripts/01_inject.py \
#     && python scripts/02_extract.py && python scripts/03_dataset.py

python scripts/05_train_gat.py --epochs 150 --seeds 5 "$@"
echo "[run_cluster] done"
