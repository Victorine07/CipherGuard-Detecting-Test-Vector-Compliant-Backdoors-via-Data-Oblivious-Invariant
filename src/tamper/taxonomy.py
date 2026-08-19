"""Tamper taxonomy T0-T6 (CipherGuard).

Labels are objective by construction (we inject the tamper). Difficulty tiers:
  easy : usually changes I/O behavior -> fails test vectors (sanity floor).
  hard : invertible and/or test-vector-passing -> where the detector earns its keep.
"""
from __future__ import annotations
from dataclasses import dataclass
from typing import Dict, List


@dataclass(frozen=True)
class TamperType:
    id: str
    name: str
    difficulty: str            # clean | easy | hard
    families: List[str]        # applicable families ("*" = all)
    expect_passes_tv: bool     # expected passes_test_vector by design
    note: str


TAXONOMY: Dict[str, TamperType] = {
    "T0": TamperType("T0", "clean", "clean", ["*"], True,
                     "unmodified reference (negative class)"),
    "T1": TamperType("T1", "round_reduction", "easy", ["*"], False,
                     "rounds cut below the literature safe margin"),
    "T2": TamperType("T2", "rotation_tamper", "hard", ["Feistel", "ARX", "SPN"], False,
                     "rotation/shift amounts changed (often still invertible)"),
    "T3": TamperType("T3", "nonlinearity_removal", "easy", ["Feistel", "ARX", "SPN"], False,
                     "nonlinear op linearized (AND->XOR / add->XOR)"),
    "T4": TamperType("T4", "sbox_weakening", "hard", ["SPN"], False,
                     "S-box replaced by a weak but bijective permutation"),
    "T5": TamperType("T5", "constant_tamper", "easy", ["*"], False,
                     "round constant / key-schedule constant bit-flipped"),
    "T6": TamperType("T6", "backdoor_tap", "hard", ["*"], True,
                     "trigger-gated key-leak backdoor; preserves the test vector"),
}

POSITIVE_TYPES = [t for t in TAXONOMY if t != "T0"]


def applicable(t: str, family: str) -> bool:
    tt = TAXONOMY[t]
    return "*" in tt.families or family in tt.families
