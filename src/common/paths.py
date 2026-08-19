"""Central path resolution for CipherGuard
"""
from __future__ import annotations
import os
from pathlib import Path

# src/common/paths.py  ->  parents[2] == project root
PROJECT_ROOT = Path(__file__).resolve().parents[2]


def _env_path(var: str, default: Path) -> Path:
    v = os.environ.get(var)
    return Path(v).expanduser().resolve() if v else default


# Inputs (read-only)
CORPUS_DIR = _env_path("CIPHERGUARD_CORPUS", PROJECT_ROOT / "new-dataset-thy-ciphers")
LEGACY_DIR = PROJECT_ROOT / "usenix-previous-implementation"
# default model dir for behavioral cross-checks (self-contained: reuses spike copies)
MODELS_DIR = _env_path("CIPHERGUARD_MODELS", PROJECT_ROOT / "spike_t6" / "cipher_lib")
# vendored third-party implementations for the conformance study (read-only, offline);
# fetched once and stored in-repo so the sweep is reproducible on an offline cluster node.
THIRDPARTY = _env_path("CIPHERGUARD_THIRDPARTY", PROJECT_ROOT / "thirdparty")

# Outputs
DATASETS = _env_path("CIPHERGUARD_DATASETS", PROJECT_ROOT / "datasets")
REGISTRY = DATASETS / "registry"
RESULTS = _env_path("CIPHERGUARD_RESULTS", PROJECT_ROOT / "results")
LOGS = _env_path("CIPHERGUARD_LOGS", PROJECT_ROOT / "logs")
REPORTS = _env_path("CIPHERGUARD_REPORTS", PROJECT_ROOT / "reports")
CHECKPOINTS = _env_path("CIPHERGUARD_CHECKPOINTS", PROJECT_ROOT / "checkpoints")


def ensure(p: Path) -> Path:
    """mkdir -p and return the path (use for every output dir)."""
    p.mkdir(parents=True, exist_ok=True)
    return p
