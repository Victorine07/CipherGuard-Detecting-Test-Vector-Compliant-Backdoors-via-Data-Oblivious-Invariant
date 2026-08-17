"""
PRESENT-64/80 block cipher (single-variant, tiered implementation).

T1: Constants
T2: Primitives (S-box layer, permutation layer, and inverses)
T3: Key schedule
T4: Orchestration (encrypt/decrypt/test)

Reference: Bogdanov et al., "PRESENT: An Ultra-Lightweight Block Cipher",
CHES 2007.
"""


WORD_SIZE = 4
BLOCK_SIZE = 64
KEY_SIZE = 80
ROUNDS = 31

SBOX = [0xC, 0x5, 0x6, 0xB, 0x9, 0x0, 0xA, 0xD, 0x3, 0xE, 0xF, 0x8, 0x4, 0x7, 0x1, 0x2]

PBOX = [
    0, 16, 32, 48, 1, 17, 33, 49, 2, 18, 34, 50, 3, 19, 35, 51,
    4, 20, 36, 52, 5, 21, 37, 53, 6, 22, 38, 54, 7, 23, 39, 55,
    8, 24, 40, 56, 9, 25, 41, 57, 10, 26, 42, 58, 11, 27, 43, 59,
    12, 28, 44, 60, 13, 29, 45, 61, 14, 30, 46, 62, 15, 31, 47, 63,
]

# Derived lookup tables (not independently specified by the cipher).
SBOX_INV = [SBOX.index(x) for x in range(16)]
PBOX_INV = [PBOX.index(x) for x in range(64)]

BLOCK_MASK = (1 << BLOCK_SIZE) - 1
KEY_MASK = (1 << KEY_SIZE) - 1


def present_64_80_sbox_layer_acc(state: int, i: int, acc: int) -> int:
    """Recursive accumulator for the S-box layer (mirrors the Isabelle
    recursive helper present_64_80_sbox_layer_acc)."""
    if i >= 16:
        return acc
    sboxed = SBOX[(state >> (i * 4)) & 0xF]
    return present_64_80_sbox_layer_acc(state, i + 1, acc | (sboxed << (i * 4)))


def present_64_80_sbox_layer(state: int) -> int:
    """Apply the 4-bit S-box to all 16 nibbles of the 64-bit state."""
    return present_64_80_sbox_layer_acc(state, 0, 0)


def present_64_80_sbox_layer_inv_acc(state: int, i: int, acc: int) -> int:
    """Recursive accumulator for the inverse S-box layer (mirrors the
    Isabelle recursive helper present_64_80_sbox_layer_inv_acc)."""
    if i >= 16:
        return acc
    sboxed = SBOX_INV[(state >> (i * 4)) & 0xF]
    return present_64_80_sbox_layer_inv_acc(state, i + 1, acc | (sboxed << (i * 4)))


def present_64_80_sbox_layer_inv(state: int) -> int:
    """Inverse S-box layer (decryption direction)."""
    return present_64_80_sbox_layer_inv_acc(state, 0, 0)


def present_64_80_permutation_layer_acc(state: int, i: int, acc: int) -> int:
    """Recursive accumulator for the bit permutation pLayer (mirrors the
    Isabelle recursive helper present_64_80_permutation_layer_acc)."""
    if i >= 64:
        return acc
    bit_val = (state >> i) & 0x1
    return present_64_80_permutation_layer_acc(state, i + 1, acc | (bit_val << PBOX[i]))


def present_64_80_permutation_layer(state: int) -> int:
    """Bit permutation pLayer: bit i moves to position PBOX[i]."""
    return present_64_80_permutation_layer_acc(state, 0, 0)


def present_64_80_permutation_layer_inv_acc(state: int, i: int, acc: int) -> int:
    """Recursive accumulator for the inverse bit permutation (mirrors the
    Isabelle recursive helper present_64_80_permutation_layer_inv_acc)."""
    if i >= 64:
        return acc
    bit_val = (state >> i) & 0x1
    return present_64_80_permutation_layer_inv_acc(state, i + 1, acc | (bit_val << PBOX_INV[i]))


def present_64_80_permutation_layer_inv(state: int) -> int:
    """Inverse bit permutation (decryption direction)."""
    return present_64_80_permutation_layer_inv_acc(state, 0, 0)


def present_64_80_update_key_register(key: int, round_counter: int) -> int:
    """
    Advance the 80-bit key register by one key-schedule step:
    rotate left 61, apply S-box to the top nibble, XOR in the
    round counter at bit position 15.
    """
    rotated = ((key & ((1 << 19) - 1)) << 61) | (key >> 19)
    top = rotated >> 76
    after_sbox = (SBOX[top] << 76) | (rotated & ((1 << 76) - 1))
    return (after_sbox ^ (round_counter << 15)) & KEY_MASK


def present_64_80_extract_round_key(key: int) -> int:
    """Extract the 64-bit round key: the top 64 bits of the key register."""
    return (key >> 16) & BLOCK_MASK


def present_64_80_generate_round_keys_acc(key: int, i: int, acc: list[int]) -> list[int]:
    """Recursive accumulator for the round-key schedule (mirrors the
    Isabelle recursive helper present_64_80_generate_round_keys_acc)."""
    if i > ROUNDS + 1:
        return acc
    rk = present_64_80_extract_round_key(key)
    next_key = present_64_80_update_key_register(key, i)
    return present_64_80_generate_round_keys_acc(next_key, i + 1, acc + [rk])


def present_64_80_generate_round_keys(master_key: int) -> list[int]:
    """Generate all 32 round keys (K1..K32) for PRESENT-64/80."""
    return present_64_80_generate_round_keys_acc(master_key & KEY_MASK, 1, [])


def present_64_80_encrypt_round(state: int, round_key: int) -> int:
    """One PRESENT round: addRoundKey, then sBoxLayer, then pLayer."""
    state ^= round_key
    state = present_64_80_sbox_layer(state)
    state = present_64_80_permutation_layer(state)
    return state


def present_64_80_decrypt_round(state: int, round_key: int) -> int:
    """Inverse PRESENT round: addRoundKey, then pLayer_inv, then sBoxLayer_inv."""
    state ^= round_key
    state = present_64_80_permutation_layer_inv(state)
    state = present_64_80_sbox_layer_inv(state)
    return state


def present_64_80_encrypt_rounds_iterate(state: int, round_keys: list[int], i: int) -> int:
    """
    Recursive encryption iterator over the 31 main rounds.
    When i == ROUNDS, apply the final round-key whitening (K32).
    """
    if i >= ROUNDS:
        return state ^ round_keys[ROUNDS]
    next_state = present_64_80_encrypt_round(state, round_keys[i])
    return present_64_80_encrypt_rounds_iterate(next_state, round_keys, i + 1)


def present_64_80_decrypt_rounds_iterate(state: int, round_keys: list[int], i: int) -> int:
    """
    Recursive decryption iterator over the 31 main rounds (round keys
    consumed K32 down to K2). When i == ROUNDS, apply final XOR with K1.
    """
    if i >= ROUNDS:
        return state ^ round_keys[0]
    round_key = round_keys[ROUNDS - i]
    next_state = present_64_80_decrypt_round(state, round_key)
    return present_64_80_decrypt_rounds_iterate(next_state, round_keys, i + 1)


def present_64_80_encrypt(plaintext: int, master_key: int) -> int:
    """Encrypt one 64-bit block under one 80-bit master key."""
    round_keys = present_64_80_generate_round_keys(master_key)
    return present_64_80_encrypt_rounds_iterate(plaintext & BLOCK_MASK, round_keys, 0)


def present_64_80_decrypt(ciphertext: int, master_key: int) -> int:
    """Decrypt one 64-bit block under one 80-bit master key."""
    round_keys = present_64_80_generate_round_keys(master_key)
    return present_64_80_decrypt_rounds_iterate(ciphertext & BLOCK_MASK, round_keys, 0)


def present_64_80_test() -> bool:
    """Official PRESENT-80 test vectors (Bogdanov et al., CHES 2007) plus round-trip checks."""
    print("=" * 60)
    print("Testing PRESENT-64/80")
    print("=" * 60)

    vectors = [
        (0x00000000000000000000, 0x0000000000000000, 0x5579C1387B228445),
        (0x00000000000000000000, 0xFFFFFFFFFFFFFFFF, 0xA112FFC72F68417B),
        (0xFFFFFFFFFFFFFFFFFFFF, 0x0000000000000000, 0xE72C46C0F5945049),
        (0xFFFFFFFFFFFFFFFFFFFF, 0xFFFFFFFFFFFFFFFF, 0x3333DCD3213210D2),
    ]

    all_ok = True
    for idx, (key, pt, expected_ct) in enumerate(vectors, start=1):
        ct = present_64_80_encrypt(pt, key)
        dec = present_64_80_decrypt(ct, key)
        ok_enc = ct == expected_ct
        ok_dec = dec == pt
        print(f"Test Vector {idx}:")
        print(f"  Key:        0x{key:020X}")
        print(f"  Plaintext:  0x{pt:016X}")
        print(f"  Ciphertext: 0x{ct:016X}")
        print(f"  Expected:   0x{expected_ct:016X}")
        print(f"  Decrypted:  0x{dec:016X}")
        print("  ✅ PASSED" if (ok_enc and ok_dec) else "  ❌ FAILED")
        all_ok = all_ok and ok_enc and ok_dec

    print()
    print("✅ All PRESENT-64/80 tests passed!" if all_ok else "❌ PRESENT-64/80 TEST FAILURE")
    print("=" * 60)
    return all_ok


if __name__ == "__main__":
    success = present_64_80_test()
    if not success:
        raise SystemExit(1)
