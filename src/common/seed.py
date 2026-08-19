"""Deterministic seeding for reproducible runs """
from __future__ import annotations
import os
import random


def set_seed(seed: int) -> int:
    """Seed Python + (if present) numpy / torch. Returns the seed for logging."""
    os.environ["PYTHONHASHSEED"] = str(seed)
    random.seed(seed)
    try:
        import numpy as np  # optional
        np.random.seed(seed)
    except Exception:
        pass
    try:
        import torch  # optional
        torch.manual_seed(seed)
        if torch.cuda.is_available():
            torch.cuda.manual_seed_all(seed)
    except Exception:
        pass
    return seed
