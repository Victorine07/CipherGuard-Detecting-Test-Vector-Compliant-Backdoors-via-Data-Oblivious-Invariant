"""Conformance testing for the Gate-2 real-data study.

Judge a third-party cipher implementation against our HOL-verified reference for the same
cipher, by (1) checking it reproduces the algorithm's official published test vectors and
(2) differential-testing it against the verified reference on random inputs. Because the
reference is machine-checked (see ``src/corpus`` + the corpus theories), a disagreement is
attributable to the third-party implementation, not to a questionable oracle.

Pure standard library; no Isabelle and no network at runtime (third-party files are vendored
under ``thirdparty/`` -- see ``thirdparty/README.md``). Consumed by ``scripts/e11_conformance.py``.
"""
from __future__ import annotations
import contextlib
import io
import json
import random
import sys
import types
from pathlib import Path

from src.common.paths import MODELS_DIR, THIRDPARTY

# Official published test vectors we anchor on, keyed by verified-reference variant stem:
# (key, plaintext, ciphertext). Extend this table as more ciphers are added to the study.
REFERENCE_VECTORS: dict[str, list[tuple[int, int, int]]] = {
    # PRESENT-80, Bogdanov et al., CHES 2007.
    "present_64_80": [
        (0x00000000000000000000, 0x0000000000000000, 0x5579C1387B228445),
        (0xFFFFFFFFFFFFFFFFFFFF, 0x0000000000000000, 0xE72C46C0F5945049),
        (0x00000000000000000000, 0xFFFFFFFFFFFFFFFF, 0xA112FFC72F68417B),
        (0xFFFFFFFFFFFFFFFFFFFF, 0xFFFFFFFFFFFFFFFF, 0x3333DCD3213210D2),
    ],
    # SIMON-32/64, official NSA test vector (Beaulieu et al.).
    "simon_32_64": [
        (0x1918111009080100, 0x65656877, 0xC69BE9BB),
    ],
    # XTEA (Needham & Wheeler), 32 cycles, big-endian words. Widely used reference vectors.
    "xtea_64_128": [
        (0x00000000000000000000000000000000, 0x0000000000000000, 0xDEE9D4D8F7131ED9),
        (0x000102030405060708090A0B0C0D0E0F, 0x4142434445464748, 0x497DF3D072612CB5),
        (0x123456789ABCDEF0FEDCBA9876543210, 0xDEADBEEFCAFEBABE, 0x8B7493AC7766389C),
    ],
    # LEA-128/128, official vector (TTAK.KO-12.0223), encoded little-endian as this reference
    # reads the 128-bit block/key (spec P=1011..1F, K=0F1E..F0, C=9FC8..8BFD in big-endian hex).
    "lea_128_128": [
        (0xF0E1D2C3B4A5968778695A4B3C2D1E0F, 0x1F1E1D1C1B1A19181716151413121110,
         0xFD8B6404A7C7325518C6C628354EC89F),
    ],
}


def variant_sizes(stem: str) -> tuple[int, int]:
    """'simon_32_64' -> (block_bits=32, key_bits=64)."""
    parts = stem.split("_")
    return int(parts[-2]), int(parts[-1])


def official_vectors(stem: str) -> list[tuple[int, int, int]]:
    return REFERENCE_VECTORS.get(stem, [])


def load_manifest(path: Path | str = THIRDPARTY / "MANIFEST.json") -> dict:
    return json.loads(Path(path).read_text())


# ----- loading implementations -------------------------------------------------------------
def _find_encrypt(ns: dict, stem: str):
    fn = ns.get(f"{stem}_encrypt")
    if fn is None:
        cands = [v for k, v in ns.items() if k.endswith("_encrypt") and callable(v)]
        fn = cands[0] if len(cands) == 1 else None
    return fn


def load_reference(stem: str, models_dir: Path = MODELS_DIR):
    """Load our HOL-verified reference and return its ``encrypt(pt, key) -> ct`` callable."""
    src = (Path(models_dir) / f"{stem}.py").read_text()
    ns: dict = {}
    exec(compile(src, f"{stem}.py", "exec"), ns)
    fn = _find_encrypt(ns, stem)
    if fn is None:
        raise RuntimeError(f"no encrypt entry found in verified reference '{stem}'")
    return fn


def load_thirdparty(path: Path | str) -> dict:
    """Load a vendored third-party module.

    Applies two compatibility shims (never to the verified reference): ``xrange`` is bound to
    ``range`` for Python-2 sources, and the legacy ``Padding`` module is stubbed (used only by
    demo code, never by block encryption). Module-level demo/main failures are tolerated because
    the class/function definitions are already bound by the time such code runs.
    """
    if "Padding" not in sys.modules:
        pad = types.ModuleType("Padding")
        pad.appendPadding = lambda s, blocksize=8, mode=0: s
        pad.removePadding = lambda s, mode=0: s
        sys.modules["Padding"] = pad
    ns: dict = {"xrange": range}
    with contextlib.redirect_stdout(io.StringIO()):
        try:
            exec(compile(Path(path).read_text(), str(path), "exec"), ns)
        except Exception:
            pass
    return ns


def build_candidate(adapter: dict, ns: dict, block_bits: int, key_bits: int):
    """Normalize a third-party interface to ``encrypt(pt:int, key:int) -> int``."""
    kind = adapter["kind"]
    if kind == "func_int":
        entry = ns[adapter["entry"]]
        return lambda pt, key: entry(pt, key)
    if kind == "func_hex":
        entry = ns[adapter["entry"]]
        ph, kh = block_bits // 4, key_bits // 4
        return lambda pt, key: int(entry(f"{pt:0{ph}x}", f"{key:0{kh}x}"), 16)
    if kind == "func_bytes":
        entry = ns[adapter["entry"]]
        pb, kb = block_bits // 8, key_bits // 8
        extra = adapter.get("extra_args", [])
        return lambda pt, key: int.from_bytes(
            entry(pt.to_bytes(pb, "big"), key.to_bytes(kb, "big"), *extra), "big")
    if kind == "class_int":
        Cls = ns[adapter["cls"]]
        return lambda pt, key: Cls(key).encrypt(pt)
    if kind == "class_bytes":
        Cls = ns[adapter["cls"]]
        kb, pb = key_bits // 8, block_bits // 8
        return lambda pt, key: int.from_bytes(
            Cls(key.to_bytes(kb, "big")).encrypt(pt.to_bytes(pb, "big")), "big")
    if kind == "class_ss":
        Cls = ns[adapter["cls"]]
        return lambda pt, key: Cls(key, key_size=key_bits, block_size=block_bits).encrypt(pt)
    raise ValueError(f"unknown adapter kind: {kind!r}")


# ----- testing -----------------------------------------------------------------------------
def _safe(f, pt, key):
    try:
        with contextlib.redirect_stdout(io.StringIO()):
            return f(pt, key)
    except Exception as e:
        return ("EXC", type(e).__name__)


def reference_official_check(stem: str, models_dir: Path = MODELS_DIR) -> tuple[int, int]:
    """How many of the official vectors our verified reference reproduces (should be all)."""
    ref = load_reference(stem, models_dir)
    vecs = official_vectors(stem)
    passed = sum(1 for (k, p, c) in vecs if ref(p, k) == c)
    return passed, len(vecs)


def differential(ref, cand, block_bits: int, key_bits: int, n: int = 1000,
                 seed: int = 20260811) -> dict:
    """Compare candidate vs reference on 2 structured edge cases + n random inputs."""
    rng = random.Random(seed)
    cases = [(0, 0), ((1 << block_bits) - 1, (1 << key_bits) - 1)]
    cases += [(rng.getrandbits(block_bits), rng.getrandbits(key_bits)) for _ in range(n)]
    agree, first = 0, None
    for pt, key in cases:
        r, t = _safe(ref, pt, key), _safe(cand, pt, key)
        if r == t:
            agree += 1
        elif first is None:
            first = (pt, key, r, t)
    return {"agree": agree, "total": len(cases), "first_disagreement": first}


def _fmt(x, block_bits: int):
    if isinstance(x, tuple):        # ("EXC", name)
        return f"{x[0]}:{x[1]}"
    return f"0x{x:0{block_bits // 4}x}"


def _fmt_disagreement(fd, block_bits: int, key_bits: int):
    if not fd:
        return None
    pt, key, r, t = fd
    return {"pt": f"0x{pt:0{block_bits // 4}x}", "key": f"0x{key:0{key_bits // 4}x}",
            "reference": _fmt(r, block_bits), "candidate": _fmt(t, block_bits)}


def assess(entry: dict, models_dir: Path = MODELS_DIR,
           thirdparty_dir: Path = THIRDPARTY, n_random: int = 1000) -> dict:
    """Assess one manifest implementation across all its declared variants."""
    ns = load_thirdparty(Path(thirdparty_dir) / entry["file"])
    per_variant, all_conform, any_error = [], True, False
    for stem in entry["variants"]:
        b, k = variant_sizes(stem)
        ref = load_reference(stem, models_dir)
        cand = build_candidate(entry["adapter"], ns, b, k)
        offs = official_vectors(stem)
        off_pass = sum(1 for (kk, pp, cc) in offs if _safe(cand, pp, kk) == cc)
        diff = differential(ref, cand, b, k, n=n_random)
        probe = _safe(cand, 0, 0)
        errored = isinstance(probe, tuple) and probe and probe[0] == "EXC"
        conform = (off_pass == len(offs)) and (diff["agree"] == diff["total"]) and not errored
        all_conform = all_conform and conform
        any_error = any_error or errored
        per_variant.append({
            "variant": stem, "block": b, "key": k,
            "official_pass": off_pass, "official_total": len(offs),
            "random_agree": diff["agree"], "random_total": diff["total"],
            "conform": conform, "errored": errored,
            "first_disagreement": _fmt_disagreement(diff["first_disagreement"], b, k),
        })
    verdict = "ERROR" if any_error else ("CONFORMING" if all_conform else "NON-CONFORMING")
    return {"label": entry["label"], "cipher": entry["cipher"], "file": entry["file"],
            "source": entry.get("source"), "expected": entry.get("expected"),
            "verdict": verdict, "variants": per_variant}
