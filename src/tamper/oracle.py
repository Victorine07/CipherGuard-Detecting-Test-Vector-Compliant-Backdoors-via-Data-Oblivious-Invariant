"""Executable oracle for the tamper engine (CipherGuard Stage 01).

Given a clean model source and a tampered model source, it measures OBJECTIVE
properties by execution:

  invertible          : dec_t(enc_t(pt,key), key) == pt over random inputs
  passes_test_vector  : tampered matches the clean reference on a known-answer
                        suite (clean model = spec, plus the official vector if the
                        model self-tests) -- the "would a defender's KAT pass?" check
  behavior_changed    : tampered differs from clean on >=1 random input (confirms an
                        injector actually did something; guards against no-op tampers)

The clean model is the specification: a KAT is (input, clean_output). "Passes" means
the tampered cipher reproduces the clean output on those inputs -- exactly the
semantics of a defender running known-answer tests.
"""
from __future__ import annotations
import contextlib
import io
import random
from typing import Any, Callable, Dict, Optional, Tuple


def _exec_module(source: str, tag: str) -> Dict[str, Any]:
    ns: Dict[str, Any] = {}
    with contextlib.redirect_stdout(io.StringIO()):
        exec(compile(source, tag, "exec"), ns)
    return ns


def _find(ns: Dict[str, Any], stem: str, suffix: str) -> Optional[Callable]:
    fn = ns.get(f"{stem}_{suffix}")
    if callable(fn):
        return fn
    for name, obj in ns.items():
        if name.endswith(f"_{suffix}") and callable(obj) \
           and not any(x in name for x in ("round", "block", "iter", "words")):
            return obj
    return None


def _official_kat(ns: Dict[str, Any], stem: str, enc: Callable) -> Optional[Tuple[int, int]]:
    """Spy the model's own self-test (if any) to grab the official (pt, key)."""
    test_fn = ns.get(f"{stem}_test")
    if not callable(test_fn):
        return None
    cap: Dict[str, int] = {}

    def spy(pt, key, *a, **k):
        cap.setdefault("pt", pt); cap.setdefault("key", key)
        return enc(pt, key, *a, **k)

    ns[f"{stem}_encrypt"] = spy
    try:
        with contextlib.redirect_stdout(io.StringIO()):
            test_fn()
        return (cap["pt"], cap["key"]) if "pt" in cap else None
    except Exception:
        return None
    finally:
        ns[f"{stem}_encrypt"] = enc


def evaluate(clean_src: str, tampered_src: str, stem: str, block: int, key: int,
             seed: int = 0, n_roundtrip: int = 48, n_kat: int = 64,
             t6_trigger: Optional[Dict[str, int]] = None) -> Dict[str, Any]:
    try:
        clean_ns = _exec_module(clean_src, f"{stem}_clean")
        tamp_ns = _exec_module(tampered_src, f"{stem}_tampered")
    except Exception as e:
        return {"ok": False, "error": f"exec failed: {e}"}

    enc_c, dec_c = _find(clean_ns, stem, "encrypt"), _find(clean_ns, stem, "decrypt")
    enc_t, dec_t = _find(tamp_ns, stem, "encrypt"), _find(tamp_ns, stem, "decrypt")
    if not all([enc_c, dec_c, enc_t, dec_t]):
        return {"ok": False, "error": "encrypt/decrypt not found"}

    bmask, kmask = (1 << block) - 1, (1 << key) - 1
    rng = random.Random(seed)
    inputs = [(rng.getrandbits(block) & bmask, rng.getrandbits(key) & kmask)
              for _ in range(max(n_roundtrip, n_kat))]

    try:
        # invertibility (tampered)
        invertible = True
        for pt, k in inputs[:n_roundtrip]:
            if dec_t(enc_t(pt, k), k) != pt:
                invertible = False
                break

        # KAT preservation: tampered == clean on the KAT suite (+ official vector)
        kat_inputs = list(inputs[:n_kat])
        off = _official_kat(clean_ns, stem, enc_c)
        if off:
            kat_inputs.insert(0, off)
        passes_tv = all(enc_t(pt, k) == enc_c(pt, k) for pt, k in kat_inputs)

        # behavior changed at all?
        behavior_changed = any(enc_t(pt, k) != enc_c(pt, k) for pt, k in inputs)

        # T6: rare-trigger leak is invisible to random sampling, so check it directly
        leaks: Optional[bool] = None
        if t6_trigger is not None:
            mask, tval = t6_trigger["trigger_mask"], t6_trigger["trigger_val"]
            t = mask.bit_length()
            pt_trig = ((rng.getrandbits(max(block - t, 1)) << t) | tval) & bmask
            secret = rng.getrandbits(key) & kmask
            leaks = (enc_t(pt_trig, secret) == (secret & bmask)) and \
                    (enc_c(pt_trig, secret) != (secret & bmask))
    except Exception as e:
        return {"ok": False, "error": f"cipher raised: {e}"}

    return {"ok": True, "invertible": bool(invertible),
            "passes_test_vector": bool(passes_tv),
            "behavior_changed": bool(behavior_changed),
            "leaks": (None if leaks is None else bool(leaks)),
            "official_kat": bool(off)}
