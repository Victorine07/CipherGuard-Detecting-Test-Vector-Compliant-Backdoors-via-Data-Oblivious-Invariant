"""
HIGHT-64/128 Block Cipher
=========================
Block size: 64 bits (8 x 8-bit bytes)
Key size: 128 bits (16 x 8-bit bytes)
Internal rounds: 32
Total stages: 34  (initial whitening + 32 rounds + final whitening)

This version is organized for fine-grained T1/T2/T3/T4 extraction
with strong isomorphic alignment to the Isabelle/HOL theory.

- T1: Constants                                      (sizes, masks, delta)
- T2: Primitives                                     (rol/ror, f0, f1, per-round transforms)
- T3: Structural Components                          (key reversal, whitening keys, key schedule)
- T4: Orchestration (bytes-level and word-level)     (encrypt/decrypt rounds iterate, wrappers)

Test vectors follow the HIGHT Internet-Draft / ArxPy reference.
"""

# ---------------------------------------------------------------------------
# T1: Constants
# ---------------------------------------------------------------------------

HIGHT_BLOCK_SIZE = 64             # bits
HIGHT_KEY_SIZE = 128              # bits
HIGHT_BLOCK_BYTES = 8
HIGHT_KEY_BYTES = 16
HIGHT_INTERNAL_ROUNDS = 32
HIGHT_TOTAL_STAGES = 34           # 1 (initial whitening) + 32 (rounds) + 1 (final whitening)
HIGHT_BYTE_MASK = 0xFF

HIGHT_DELTA = [
    0x5A, 0x6D, 0x36, 0x1B, 0x0D, 0x06, 0x03, 0x41,
    0x60, 0x30, 0x18, 0x4C, 0x66, 0x33, 0x59, 0x2C,
    0x56, 0x2B, 0x15, 0x4A, 0x65, 0x72, 0x39, 0x1C,
    0x4E, 0x67, 0x73, 0x79, 0x3C, 0x5E, 0x6F, 0x37,
    0x5B, 0x2D, 0x16, 0x0B, 0x05, 0x42, 0x21, 0x50,
    0x28, 0x54, 0x2A, 0x55, 0x6A, 0x75, 0x7A, 0x7D,
    0x3E, 0x5F, 0x2F, 0x17, 0x4B, 0x25, 0x52, 0x29,
    0x14, 0x0A, 0x45, 0x62, 0x31, 0x58, 0x6C, 0x76,
    0x3B, 0x1D, 0x0E, 0x47, 0x63, 0x71, 0x78, 0x7C,
    0x7E, 0x7F, 0x3F, 0x1F, 0x0F, 0x07, 0x43, 0x61,
    0x70, 0x38, 0x5C, 0x6E, 0x77, 0x7B, 0x3D, 0x1E,
    0x4F, 0x27, 0x53, 0x69, 0x34, 0x1A, 0x4D, 0x26,
    0x13, 0x49, 0x24, 0x12, 0x09, 0x04, 0x02, 0x01,
    0x40, 0x20, 0x10, 0x08, 0x44, 0x22, 0x11, 0x48,
    0x64, 0x32, 0x19, 0x0C, 0x46, 0x23, 0x51, 0x68,
    0x74, 0x3A, 0x5D, 0x2E, 0x57, 0x6B, 0x35, 0x5A,
]


# ---------------------------------------------------------------------------
# T2: Primitives
# ---------------------------------------------------------------------------

def hight_rol8(x: int, n: int) -> int:
    """Rotate left on 8-bit words (matches Isabelle word_rotl on 8-word)."""
    n = n % 8
    return ((x << n) | (x >> (8 - n))) & HIGHT_BYTE_MASK


def hight_ror8(x: int, n: int) -> int:
    """Rotate right on 8-bit words (matches Isabelle word_rotr on 8-word)."""
    n = n % 8
    return ((x >> n) | (x << (8 - n))) & HIGHT_BYTE_MASK


def hight_f0(x: int) -> int:
    """F0: ROL1 ^ ROL2 ^ ROL7."""
    return hight_rol8(x, 1) ^ hight_rol8(x, 2) ^ hight_rol8(x, 7)


def hight_f1(x: int) -> int:
    """F1: ROL3 ^ ROL4 ^ ROL6."""
    return hight_rol8(x, 3) ^ hight_rol8(x, 4) ^ hight_rol8(x, 6)


def hight_initial_transformation(
    state: list[int], wk0: int, wk1: int, wk2: int, wk3: int
) -> list[int]:
    """Initial whitening transform (bytes reversed already handled by caller)."""
    if len(state) != HIGHT_BLOCK_BYTES:
        raise ValueError(f"Expected {HIGHT_BLOCK_BYTES} state bytes, got {len(state)}")

    result = state[:]
    result[0] = (result[0] + wk0) & HIGHT_BYTE_MASK
    result[2] ^= wk1
    result[4] = (result[4] + wk2) & HIGHT_BYTE_MASK
    result[6] ^= wk3
    return result


def hight_initial_transformation_inv(
    state: list[int], wk0: int, wk1: int, wk2: int, wk3: int
) -> list[int]:
    """Inverse of initial whitening transform."""
    if len(state) != HIGHT_BLOCK_BYTES:
        raise ValueError(f"Expected {HIGHT_BLOCK_BYTES} state bytes, got {len(state)}")

    result = state[:]
    result[0] = (result[0] - wk0) & HIGHT_BYTE_MASK
    result[2] ^= wk1
    result[4] = (result[4] - wk2) & HIGHT_BYTE_MASK
    result[6] ^= wk3
    return result


def hight_encrypt_round(
    state: list[int], sk0: int, sk1: int, sk2: int, sk3: int
) -> list[int]:
    """One HIGHT encryption round (Fig. 3 semantics, typo-corrected)."""
    if len(state) != HIGHT_BLOCK_BYTES:
        raise ValueError(f"Expected {HIGHT_BLOCK_BYTES} state bytes, got {len(state)}")

    result = [0] * HIGHT_BLOCK_BYTES
    result[1] = state[0]
    result[3] = state[2]
    result[5] = state[4]
    result[7] = state[6]

    result[0] = state[7] ^ ((hight_f0(state[6]) + sk3) & HIGHT_BYTE_MASK)
    result[2] = (state[1] + (hight_f1(state[0]) ^ sk0)) & HIGHT_BYTE_MASK
    result[4] = state[3] ^ ((hight_f0(state[2]) + sk1) & HIGHT_BYTE_MASK)
    result[6] = (state[5] + (hight_f1(state[4]) ^ sk2)) & HIGHT_BYTE_MASK
    return result


def hight_decrypt_round(
    state: list[int], sk0: int, sk1: int, sk2: int, sk3: int
) -> list[int]:
    """One HIGHT decryption round, inverse of hight_encrypt_round."""
    if len(state) != HIGHT_BLOCK_BYTES:
        raise ValueError(f"Expected {HIGHT_BLOCK_BYTES} state bytes, got {len(state)}")

    result = [0] * HIGHT_BLOCK_BYTES
    result[0] = state[1]
    result[1] = (state[2] - (hight_f1(state[1]) ^ sk0)) & HIGHT_BYTE_MASK
    result[2] = state[3]
    result[3] = state[4] ^ ((hight_f0(state[3]) + sk1) & HIGHT_BYTE_MASK)
    result[4] = state[5]
    result[5] = (state[6] - (hight_f1(state[5]) ^ sk2)) & HIGHT_BYTE_MASK
    result[6] = state[7]
    result[7] = state[0] ^ ((hight_f0(state[7]) + sk3) & HIGHT_BYTE_MASK)
    return result


def hight_final_transformation(
    state: list[int], wk4: int, wk5: int, wk6: int, wk7: int
) -> list[int]:
    """Final whitening transform."""
    if len(state) != HIGHT_BLOCK_BYTES:
        raise ValueError(f"Expected {HIGHT_BLOCK_BYTES} state bytes, got {len(state)}")

    result = [0] * HIGHT_BLOCK_BYTES
    result[0] = (state[1] + wk4) & HIGHT_BYTE_MASK
    result[1] = state[2]
    result[2] = state[3] ^ wk5
    result[3] = state[4]
    result[4] = (state[5] + wk6) & HIGHT_BYTE_MASK
    result[5] = state[6]
    result[6] = state[7] ^ wk7
    result[7] = state[0]
    return result


def hight_final_transformation_inv(
    state: list[int], wk4: int, wk5: int, wk6: int, wk7: int
) -> list[int]:
    """Inverse of final whitening transform."""
    if len(state) != HIGHT_BLOCK_BYTES:
        raise ValueError(f"Expected {HIGHT_BLOCK_BYTES} state bytes, got {len(state)}")

    result = [0] * HIGHT_BLOCK_BYTES
    result[0] = state[7]
    result[1] = (state[0] - wk4) & HIGHT_BYTE_MASK
    result[2] = state[1]
    result[3] = state[2] ^ wk5
    result[4] = state[3]
    result[5] = (state[4] - wk6) & HIGHT_BYTE_MASK
    result[6] = state[5]
    result[7] = state[6] ^ wk7
    return result


# ---------------------------------------------------------------------------
# T3: Structural Components (Key schedule)
# ---------------------------------------------------------------------------

def hight_reverse_master_key(master_key: tuple[int, ...]) -> list[int]:
    """Reverse master key bytes (ArxPy style: mk[i] = m_{15-i})."""
    if len(master_key) != HIGHT_KEY_BYTES:
        raise ValueError(f"HIGHT requires {HIGHT_KEY_BYTES} key bytes")
    return [b & HIGHT_BYTE_MASK for b in reversed(master_key)]


def hight_initial_whitening_keys(reversed_master_key: list[int]) -> list[int]:
    """Extract wk0..wk3 from reversed master key."""
    if len(reversed_master_key) != HIGHT_KEY_BYTES:
        raise ValueError("Reversed master key must contain 16 bytes")
    return [reversed_master_key[i + 12] & HIGHT_BYTE_MASK for i in range(4)]


def hight_final_whitening_keys(reversed_master_key: list[int]) -> list[int]:
    """Extract wk4..wk7 from reversed master key."""
    if len(reversed_master_key) != HIGHT_KEY_BYTES:
        raise ValueError("Reversed master key must contain 16 bytes")
    return [reversed_master_key[i] & HIGHT_BYTE_MASK for i in range(4)]


def hight_whitening_keys(reversed_master_key: list[int]) -> list[int]:
    """Convenience: concatenated initial + final whitening keys."""
    return hight_initial_whitening_keys(reversed_master_key) + hight_final_whitening_keys(reversed_master_key)


def hight_subkeys_for_round_scan(
    reversed_master_key: list[int], round_i: int
) -> list[int]:
    """
    Internal scan matching Isabelle hight_64_128_subkeys_for_round_scan:
    collects exactly 4 subkeys for round_i using the delta table and rMK.
    """
    if len(reversed_master_key) != HIGHT_KEY_BYTES:
        raise ValueError("Reversed master key must contain 16 bytes")
    if not (0 <= round_i < HIGHT_INTERNAL_ROUNDS):
        raise ValueError(f"round_i must be in [0, {HIGHT_INTERNAL_ROUNDS - 1}]")

    subkeys: list[int] = []
    base = 4 * round_i
    start = base
    end = base + 4

    for i in range(8):
        for j in range(8):
            idx = 16 * i + j
            if start <= idx < end:
                value = (reversed_master_key[(j - i) % 8] + HIGHT_DELTA[idx]) & HIGHT_BYTE_MASK
                subkeys.append(value)
            elif start <= idx + 8 < end:
                value = (reversed_master_key[((j - i) % 8) + 8] + HIGHT_DELTA[idx + 8]) & HIGHT_BYTE_MASK
                subkeys.append(value)

    return subkeys


def hight_subkeys_for_round(
    reversed_master_key: list[int], round_i: int
) -> list[int]:
    """Return 4 round subkeys for round_i (post-scan sanity check)."""
    subkeys = hight_subkeys_for_round_scan(reversed_master_key, round_i)
    if len(subkeys) != 4:
        raise ValueError(f"Expected 4 subkeys for round {round_i}, got {len(subkeys)}")
    return subkeys


def hight_generate_round_keys_rec(
    reversed_master_key: list[int], round_i: int
) -> list[int]:
    """Recursive key schedule, appending 4 subkeys per round."""
    if round_i >= HIGHT_INTERNAL_ROUNDS:
        return []
    return (
        hight_subkeys_for_round(reversed_master_key, round_i)
        + hight_generate_round_keys_rec(reversed_master_key, round_i + 1)
    )


def hight_generate_round_keys(master_key: tuple[int, ...]) -> list[int]:
    """
    Generate full round key schedule:
    [wk0..wk3] ++ [sk for round 0..31] ++ [wk4..wk7]
    length = 4 * HIGHT_TOTAL_STAGES = 136 bytes.
    """
    rMK = hight_reverse_master_key(master_key)
    initial_keys = hight_initial_whitening_keys(rMK)
    round_subkeys = hight_generate_round_keys_rec(rMK, 0)
    final_keys = hight_final_whitening_keys(rMK)
    round_keys = initial_keys + round_subkeys + final_keys

    expected_len = 4 * HIGHT_TOTAL_STAGES
    if len(round_keys) != expected_len:
        raise ValueError(f"Expected {expected_len} round-key bytes, got {len(round_keys)}")
    return round_keys


# ---------------------------------------------------------------------------
# T4: Orchestration (round iteration, bytes-level)
# ---------------------------------------------------------------------------

def hight_encrypt_rounds_step(
    state: list[int], round_keys: list[int], round_i: int
) -> list[int]:
    """Extract SK for round_i from round_keys and apply one encrypt round."""
    base = 4 + 4 * round_i
    sk0, sk1, sk2, sk3 = round_keys[base: base + 4]
    return hight_encrypt_round(state, sk0, sk1, sk2, sk3)


def hight_decrypt_rounds_step(
    state: list[int], round_keys: list[int], i: int
) -> list[int]:
    """
    Helper for decryption iteration: given logical step index i (from 0 up),
    compute real round index round_i = (R-1) - i and apply decrypt round.
    """
    round_i = (HIGHT_INTERNAL_ROUNDS - 1) - i
    base = 4 + 4 * round_i
    sk0, sk1, sk2, sk3 = round_keys[base: base + 4]
    return hight_decrypt_round(state, sk0, sk1, sk2, sk3)


def hight_encrypt_rounds_iterate(
    state: list[int], round_keys: list[int], round_i: int
) -> list[int]:
    """
    Recursive encrypt iterator over internal rounds.
    When round_i == HIGHT_INTERNAL_ROUNDS, apply final whitening.
    """
    if round_i >= HIGHT_INTERNAL_ROUNDS:
        wk4, wk5, wk6, wk7 = round_keys[-4:]
        return hight_final_transformation(state, wk4, wk5, wk6, wk7)

    next_state = hight_encrypt_rounds_step(state, round_keys, round_i)
    return hight_encrypt_rounds_iterate(next_state, round_keys, round_i + 1)


def hight_decrypt_rounds_iterate(
    state: list[int], round_keys: list[int], i: int
) -> list[int]:
    """
    Recursive decrypt iterator over internal rounds.
    When i == HIGHT_INTERNAL_ROUNDS, stop (core rounds done).
    """
    if i >= HIGHT_INTERNAL_ROUNDS:
        return state
    next_state = hight_decrypt_rounds_step(state, round_keys, i)
    return hight_decrypt_rounds_iterate(next_state, round_keys, i + 1)


def hight_encrypt_bytes(
    plaintext: tuple[int, ...], master_key: tuple[int, ...]
) -> tuple[int, ...]:
    """Top-level encryption on 8 bytes and 16-byte key."""
    if len(plaintext) != HIGHT_BLOCK_BYTES:
        raise ValueError(f"HIGHT requires {HIGHT_BLOCK_BYTES}-byte plaintext blocks")
    if len(master_key) != HIGHT_KEY_BYTES:
        raise ValueError(f"HIGHT requires {HIGHT_KEY_BYTES}-byte master keys")

    round_keys = hight_generate_round_keys(master_key)

    # reverse bytes to match Isabelle / ArxPy convention
    state = list(reversed(plaintext))

    # initial whitening
    wk0, wk1, wk2, wk3 = round_keys[0:4]
    state = hight_initial_transformation(state, wk0, wk1, wk2, wk3)

    # internal rounds + final whitening
    state = hight_encrypt_rounds_iterate(state, round_keys, 0)

    # reverse back
    return tuple(reversed(state))


def hight_decrypt_bytes(
    ciphertext: tuple[int, ...], master_key: tuple[int, ...]
) -> tuple[int, ...]:
    """Top-level decryption on 8 bytes and 16-byte key."""
    if len(ciphertext) != HIGHT_BLOCK_BYTES:
        raise ValueError(f"HIGHT requires {HIGHT_BLOCK_BYTES}-byte ciphertext blocks")
    if len(master_key) != HIGHT_KEY_BYTES:
        raise ValueError(f"HIGHT requires {HIGHT_KEY_BYTES}-byte master keys")

    round_keys = hight_generate_round_keys(master_key)

    # reverse bytes as in encrypt
    state = list(reversed(ciphertext))

    # undo final whitening first (wk4..wk7 at the end of schedule)
    wk4, wk5, wk6, wk7 = round_keys[-4:]
    state = hight_final_transformation_inv(state, wk4, wk5, wk6, wk7)

    # run internal rounds in reverse order, but via logical iterator
    state = hight_decrypt_rounds_iterate(state, round_keys, 0)

    # undo initial whitening last
    wk0, wk1, wk2, wk3 = round_keys[0:4]
    state = hight_initial_transformation_inv(state, wk0, wk1, wk2, wk3)

    # reverse back
    return tuple(reversed(state))


# ---------------------------------------------------------------------------
# T4: Integer/byte wrappers (64-bit block, 128-bit key)
# ---------------------------------------------------------------------------

def hight_block_to_bytes(block: int) -> list[int]:
    """Convert 64-bit integer block to list of 8 bytes (big-endian)."""
    return [(block >> (8 * i)) & HIGHT_BYTE_MASK for i in range(7, -1, -1)]


def hight_bytes_to_block(bytes_list: list[int]) -> int:
    """Convert list of 8 bytes (big-endian) back to 64-bit integer."""
    if len(bytes_list) != HIGHT_BLOCK_BYTES:
        raise ValueError(f"Expected {HIGHT_BLOCK_BYTES} bytes, got {len(bytes_list)}")
    value = 0
    for b in bytes_list:
        value = (value << 8) | (b & HIGHT_BYTE_MASK)
    return value


def hight_64_128_int_to_key_bytes(key_int: int) -> tuple[int, ...]:
    """Convert 128-bit integer key to tuple of 16 bytes (big-endian)."""
    return tuple((key_int >> (8 * i)) & HIGHT_BYTE_MASK for i in range(15, -1, -1))


def hight_encrypt(plaintext: int, master_key: int) -> int:
    """Encrypt 64-bit integer under 128-bit integer key."""
    plaintext_bytes = tuple(hight_block_to_bytes(plaintext))
    key_bytes = hight_64_128_int_to_key_bytes(master_key)
    ciphertext_bytes = hight_encrypt_bytes(plaintext_bytes, key_bytes)
    return hight_bytes_to_block(list(ciphertext_bytes))


def hight_decrypt(ciphertext: int, master_key: int) -> int:
    """Decrypt 64-bit integer under 128-bit integer key."""
    ciphertext_bytes = tuple(hight_block_to_bytes(ciphertext))
    key_bytes = hight_64_128_int_to_key_bytes(master_key)
    plaintext_bytes = hight_decrypt_bytes(ciphertext_bytes, key_bytes)
    return hight_bytes_to_block(list(plaintext_bytes))


# ---------------------------------------------------------------------------
# Test vectors (HIGHT Internet-Draft / ArxPy reference)
# ---------------------------------------------------------------------------

def test_hight_vectors() -> bool:
    pt1 = (0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00)
    key1 = (0x00, 0x11, 0x22, 0x33, 0x44, 0x55, 0x66, 0x77,
            0x88, 0x99, 0xAA, 0xBB, 0xCC, 0xDD, 0xEE, 0xFF)
    expected1 = (0x00, 0xF4, 0x18, 0xAE, 0xD9, 0x4F, 0x03, 0xF2)

    pt2 = (0x00, 0x11, 0x22, 0x33, 0x44, 0x55, 0x66, 0x77)
    key2 = (0xFF, 0xEE, 0xDD, 0xCC, 0xBB, 0xAA, 0x99, 0x88,
            0x77, 0x66, 0x55, 0x44, 0x33, 0x22, 0x11, 0x00)
    expected2 = (0x23, 0xCE, 0x9F, 0x72, 0xE5, 0x43, 0xE6, 0xD8)

    ct1 = hight_encrypt_bytes(pt1, key1)
    ct2 = hight_encrypt_bytes(pt2, key2)

    dec1 = hight_decrypt_bytes(ct1, key1)
    dec2 = hight_decrypt_bytes(ct2, key2)

    ok1 = ct1 == expected1
    ok2 = ct2 == expected2
    ok3 = dec1 == pt1
    ok4 = dec2 == pt2

    print("HIGHT encrypt vector 1:", "PASS" if ok1 else f"FAIL got={ct1} expected={expected1}")
    print("HIGHT encrypt vector 2:", "PASS" if ok2 else f"FAIL got={ct2} expected={expected2}")
    print("HIGHT decrypt vector 1:", "PASS" if ok3 else f"FAIL got={dec1} expected={pt1}")
    print("HIGHT decrypt vector 2:", "PASS" if ok4 else f"FAIL got={dec2} expected={pt2}")
    return ok1 and ok2 and ok3 and ok4


if __name__ == "__main__":
    success = test_hight_vectors()
    print("ALL TESTS PASSED" if success else "TEST FAILURE")