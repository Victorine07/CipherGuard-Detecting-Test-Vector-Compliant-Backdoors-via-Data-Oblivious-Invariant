"""Corpus verification for Stage 00 (CipherGuard).

Ground truth ultimately comes from Isabelle (test-vector + invertibility lemmas).
Compute nodes have no Isabelle, so verification is a
separable, cached concern with three honest outcomes per variant:

  * isabelle_available : an Isabelle install is on PATH -> a full HOL session
    runner would go here (not implemented in this stage; run the offline build
    to populate). We do NOT fake a HOL result.
  * behavioral         : no Isabelle, but an executable Python model exists that
    mirrors the theory -> we cross-check invertibility (roundtrip) and, if the
    model ships a self-test, the official test vector.
  * pending            : neither -> recorded truthfully, never guessed.

The behavioral check is evidence, not proof: it validates that the reference
model reproduces the intended behavior, which anchors the registry until a real
HOL build runs.
"""
from __future__ import annotations
import contextlib
import importlib.util
import io
import random
import shutil
from pathlib import Path
from typing import Any, Dict, Optional

from ..common.paths import MODELS_DIR
from .thy_parser import parse_variant_name


def _load_model(stem: str, models_dir: Path):
    p = models_dir / f"{stem}.py"
    if not p.exists():
        return None
    spec = importlib.util.spec_from_file_location(f"cg_verify_{stem}", p)
    mod = importlib.util.module_from_spec(spec)
    with contextlib.redirect_stdout(io.StringIO()):
        spec.loader.exec_module(mod)
    return mod


def _fn(mod, stem: str, suffix: str):
    fn = getattr(mod, f"{stem}_{suffix}", None)
    if callable(fn):
        return fn
    for name in dir(mod):
        if name.endswith(f"_{suffix}") and callable(getattr(mod, name)) \
           and not any(x in name for x in ("round", "block", "iter", "words")):
            return getattr(mod, name)
    return None


def verify_variant(variant: str, models_dir: Path = MODELS_DIR,
                   n_roundtrip: int = 64, seed: int = 0) -> Dict[str, Any]:
    if shutil.which("isabelle"):
        return {"status": "isabelle_available", "method": "hol",
                "test_vector": None, "invertibility": None,
                "notes": "Isabelle on PATH; run offline HOL build to populate (not done in this stage)."}

    _, block, key = parse_variant_name(variant)
    stem = variant.lower()
    mod = _load_model(stem, models_dir)
    if mod is None:
        return {"status": "pending", "method": "none", "test_vector": None,
                "invertibility": None,
                "notes": f"no Isabelle and no Python model ({stem}.py) for behavioral cross-check"}

    enc, dec = _fn(mod, stem, "encrypt"), _fn(mod, stem, "decrypt")
    if enc is None or dec is None or block is None or key is None:
        return {"status": "pending", "method": "model_incomplete", "test_vector": None,
                "invertibility": None, "notes": f"model {stem}.py missing encrypt/decrypt or sizes"}

    block_mask, key_mask = (1 << block) - 1, (1 << key) - 1
    rng = random.Random(seed)
    invertible = True
    for _ in range(n_roundtrip):
        pt, k = rng.getrandbits(block) & block_mask, rng.getrandbits(key) & key_mask
        try:
            if dec(enc(pt, k), k) != pt:
                invertible = False
                break
        except Exception as e:
            return {"status": "error", "method": "behavioral", "test_vector": None,
                    "invertibility": None, "notes": f"model raised: {e}"}

    # official test vector via the model's own self-test, if present
    tv: Optional[bool] = None
    test_fn = getattr(mod, f"{stem}_test", None)
    if callable(test_fn):
        try:
            with contextlib.redirect_stdout(io.StringIO()):
                test_fn()
            tv = True
        except AssertionError:
            tv = False
        except Exception:
            tv = None

    return {"status": "behavioral", "method": "python_model", "model_file": f"{stem}.py",
            "invertibility": invertible, "test_vector": tv,
            "roundtrips": n_roundtrip,
            "notes": "behavioral cross-check (evidence, not HOL proof)"}
