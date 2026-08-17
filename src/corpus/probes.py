"""Reference-free cryptographic property probes (CipherGuard detection layer L2).

The structural invariant check (L1) catches trigger/leak backdoors, which inject secret-dependent
control flow or a key-to-output shortcut. It does NOT catch *weakenings* that degrade a cipher's
cryptographic strength without adding such structure --- a weakened S-box or a linearized round
still routes the key only through the key schedule and never branches on a secret. L2 catches those
by measuring cryptographic properties of the executed implementation and flagging deviations from
the manifold of the clean, machine-checked corpus.

Crucially these probes are NON-CIRCULAR: a weakened cipher fails them for genuine cryptographic
reasons (an identity S-box really has zero nonlinearity; a linearized round really becomes affine),
not because we injected a signature the detector was built to match. The clean manifold, and hence
the thresholds, are derived from the verified corpus rather than chosen by hand.

Probes (all reference-free; we execute the untrusted encrypt(pt,key)->ct):
  * diffusion completeness : fraction of (input bit i, output bit j) pairs where flipping input
                             bit i ever flips output bit j. A full cipher reaches ~1.0.
  * strict avalanche (SAC) : mean fraction of output bits flipped by a single input-bit flip (~0.5).
  * affine-relation rate   : Pr[ E(x)^E(y)^E(x^y)^E(0) == 0 ]. A (partly) linearized cipher sits
                             far above the ~2^-n baseline of a clean cipher.
"""
from __future__ import annotations
import random
from statistics import mean


def diffusion_and_sac(enc, n: int, kbits: int, rng: random.Random, m: int):
    """Return (diffusion_completeness in [0,1], strict-avalanche in [0,1])."""
    dep = [[False] * n for _ in range(n)]
    flips = 0
    trials = 0
    for _ in range(m):
        pt = rng.getrandbits(n)
        key = rng.getrandbits(kbits)
        c0 = enc(pt, key)
        for i in range(n):
            diff = c0 ^ enc(pt ^ (1 << i), key)
            flips += bin(diff).count("1")
            trials += n
            for j in range(n):
                if (diff >> j) & 1:
                    dep[i][j] = True
    completeness = sum(1 for row in dep for cell in row if cell) / (n * n)
    sac = flips / trials if trials else 0.0
    return completeness, sac


def affine_rate(enc, n: int, kbits: int, rng: random.Random, m: int) -> float:
    """Pr[ E(x)^E(y)^E(x^y)^E(0) == 0 ] over random x,y with one fixed key."""
    key = rng.getrandbits(kbits)
    e0 = enc(0, key)
    ok = 0
    for _ in range(m):
        x = rng.getrandbits(n)
        y = rng.getrandbits(n)
        if (enc(x, key) ^ enc(y, key) ^ enc(x ^ y, key) ^ e0) == 0:
            ok += 1
    return ok / m


def probe_vector(enc, n: int, kbits: int, seed: int = 1) -> dict:
    """Compute the property-probe vector for one implementation. Sample budget scales down for
    larger blocks to keep the cost bounded; the signal (full vs collapsed diffusion, affine vs
    non-affine) is large and robust to the exact budget."""
    m_diff = 40 if n <= 64 else 20
    comp, sac = diffusion_and_sac(enc, n, kbits, random.Random(seed), m_diff)
    aff = affine_rate(enc, n, kbits, random.Random(seed + 7), m=200)
    return {"diffusion": round(comp, 4), "sac": round(sac, 4), "affine_rate": round(aff, 6)}


def calibrate(clean_vectors: list[dict]) -> dict:
    """Derive L2 thresholds from the clean corpus manifold (no hand-picked constants).

    Clean lightweight ciphers reach full diffusion and behave as non-affine permutations, so the
    clean manifold is tight: diffusion ~1.0, |SAC-0.5| small, affine_rate ~0. We set each threshold
    just outside the observed clean range, so a clean cipher is never flagged and any measurable
    degradation is."""
    diffs = [v["diffusion"] for v in clean_vectors]
    sac_dev = [abs(v["sac"] - 0.5) for v in clean_vectors]
    affs = [v["affine_rate"] for v in clean_vectors]
    return {
        "diffusion_min": min(diffs),
        "sac_dev_max": max(sac_dev),
        "affine_max": max(affs),
        # margins: half a percent of diffusion, and a clear gap above the clean affine ceiling
        "diffusion_thresh": min(diffs) - 0.005,
        "sac_dev_thresh": max(sac_dev) + 0.03,
        "affine_thresh": max(max(affs) * 4, 0.02),
    }


def flags(vec: dict, thr: dict) -> list[str]:
    """Which probes flag this implementation as anomalous vs the clean manifold."""
    out = []
    if vec["diffusion"] < thr["diffusion_thresh"]:
        out.append("diffusion")
    if abs(vec["sac"] - 0.5) > thr["sac_dev_thresh"]:
        out.append("sac")
    if vec["affine_rate"] > thr["affine_thresh"]:
        out.append("affine")
    return out


def is_flagged(vec: dict, thr: dict) -> bool:
    return bool(flags(vec, thr))
