"""Literature-derived attack data + cipher family map (CipherGuard).
"""
from __future__ import annotations
from typing import Dict, Optional, Tuple

# (block, key) -> {total_rounds, rounds_broken, attack_type, complexity_log2}
ATTACK_DB: Dict[str, Dict[Tuple[int, int], dict]] = {
    "Simon": {
        (32, 64): {"total_rounds": 32, "rounds_broken": 24, "attack_type": "integral"},
        (48, 72): {"total_rounds": 36, "rounds_broken": 24, "attack_type": "linear_hull"},
        (48, 96): {"total_rounds": 36, "rounds_broken": 25, "attack_type": "linear_hull"},
        (64, 96): {"total_rounds": 42, "rounds_broken": 30, "attack_type": "linear_hull"},
        (64, 128): {"total_rounds": 44, "rounds_broken": 31, "attack_type": "linear_hull"},
        (96, 96): {"total_rounds": 52, "rounds_broken": 37, "attack_type": "linear_hull"},
        (96, 144): {"total_rounds": 54, "rounds_broken": 38, "attack_type": "linear_hull"},
        (128, 128): {"total_rounds": 68, "rounds_broken": 49, "attack_type": "linear_hull"},
        (128, 192): {"total_rounds": 69, "rounds_broken": 51, "attack_type": "linear_hull"},
        (128, 256): {"total_rounds": 72, "rounds_broken": 53, "attack_type": "linear_hull"},
    },
    "Speck": {
        (32, 64): {"total_rounds": 22, "rounds_broken": 15, "attack_type": "differential"},
        (48, 72): {"total_rounds": 22, "rounds_broken": 16, "attack_type": "differential"},
        (48, 96): {"total_rounds": 23, "rounds_broken": 17, "attack_type": "differential"},
        (64, 96): {"total_rounds": 26, "rounds_broken": 19, "attack_type": "differential"},
        (64, 128): {"total_rounds": 27, "rounds_broken": 20, "attack_type": "differential"},
        (96, 96): {"total_rounds": 28, "rounds_broken": 20, "attack_type": "differential"},
        (96, 144): {"total_rounds": 29, "rounds_broken": 21, "attack_type": "differential"},
        (128, 128): {"total_rounds": 32, "rounds_broken": 23, "attack_type": "differential"},
        (128, 192): {"total_rounds": 33, "rounds_broken": 24, "attack_type": "differential"},
        (128, 256): {"total_rounds": 34, "rounds_broken": 25, "attack_type": "differential"},
    },
    "Present": {
        (64, 80): {"total_rounds": 31, "rounds_broken": 26, "attack_type": "linear"},
        (64, 128): {"total_rounds": 31, "rounds_broken": 26, "attack_type": "differential"},
    },
    "Hight": {
        (64, 128): {"total_rounds": 32, "rounds_broken": 26, "attack_type": "biclique"},
    },
}

# family classification by base cipher name (lowercased)
FAMILY: Dict[str, str] = {
    "simon": "Feistel", "simeck": "Feistel", "xtea": "Feistel",
    "speck": "ARX", "lea": "ARX", "hight": "ARX", "cham": "ARX",
    "present": "SPN", "gift": "SPN", "gift_cofb": "SPN", "rectangle": "SPN",
    "sparx": "SPN", "skinny": "SPN",
    "ascon": "AEAD",
}


def family_of(base_cipher: str) -> str:
    return FAMILY.get(base_cipher.lower(), "Unknown")


def safe_round_margin(base_cipher: str, block: int, key: int) -> Optional[dict]:
    """Return {total_rounds, rounds_broken, broken_at_or_below, attack_type} from the
    literature, or None if we have no data for this variant."""
    entry = ATTACK_DB.get(base_cipher.capitalize(), {}).get((block, key))
    if not entry:
        return None
    return {
        "total_rounds": entry["total_rounds"],
        "rounds_broken": entry["rounds_broken"],
        "broken_at_or_below": entry["rounds_broken"],
        "attack_type": entry["attack_type"],
        "source": "cryptanalytic literature (ported ATTACK_DB)",
    }
