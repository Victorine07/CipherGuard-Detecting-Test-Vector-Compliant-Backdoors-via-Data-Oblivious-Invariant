"""
GIFT-128/128 block cipher (single-variant, tiered implementation).

T1: Constants
T2: Primitives (S-box layer, permutation layer, and inverses)
T3: Key schedule
T4: Orchestration (encrypt/decrypt/test)

Reference: Banik, Pandey, Peyrin, Sasaki, Sim, Todo, "GIFT: A Small
Present Towards Reaching the Limit of Lightweight Encryption", CHES 2017
(eprint.iacr.org/2017/622). Round structure, S-box, bit permutation and
key schedule ported from the designers' own reference implementation
(github.com/giftcipher/gift, GIFT128-128_cipher.cpp).
"""


WORD_SIZE = 4
BLOCK_SIZE = 128
KEY_SIZE = 128
ROUNDS = 40

SBOX = [1, 10, 4, 12, 6, 15, 3, 9, 2, 13, 11, 7, 5, 0, 8, 14]

PBOX = [
    0, 33, 66, 99, 96, 1, 34, 67, 64, 97, 2, 35, 32, 65, 98, 3,
    4, 37, 70, 103, 100, 5, 38, 71, 68, 101, 6, 39, 36, 69, 102, 7,
    8, 41, 74, 107, 104, 9, 42, 75, 72, 105, 10, 43, 40, 73, 106, 11,
    12, 45, 78, 111, 108, 13, 46, 79, 76, 109, 14, 47, 44, 77, 110, 15,
    16, 49, 82, 115, 112, 17, 50, 83, 80, 113, 18, 51, 48, 81, 114, 19,
    20, 53, 86, 119, 116, 21, 54, 87, 84, 117, 22, 55, 52, 85, 118, 23,
    24, 57, 90, 123, 120, 25, 58, 91, 88, 121, 26, 59, 56, 89, 122, 27,
    28, 61, 94, 127, 124, 29, 62, 95, 92, 125, 30, 63, 60, 93, 126, 31,
]

RC = [
    0x01, 0x03, 0x07, 0x0F, 0x1F, 0x3E, 0x3D, 0x3B, 0x37, 0x2F,
    0x1E, 0x3C, 0x39, 0x33, 0x27, 0x0E, 0x1D, 0x3A, 0x35, 0x2B,
    0x16, 0x2C, 0x18, 0x30, 0x21, 0x02, 0x05, 0x0B, 0x17, 0x2E,
    0x1C, 0x38, 0x31, 0x23, 0x06, 0x0D, 0x1B, 0x36, 0x2D, 0x1A,
    0x34, 0x29, 0x12, 0x24, 0x08, 0x11, 0x22, 0x04, 0x09, 0x13,
    0x26, 0x0C, 0x19, 0x32, 0x25, 0x0A, 0x15, 0x2A, 0x14, 0x28,
    0x10, 0x20,
]

# Derived lookup tables (not independently specified by the cipher).
SBOX_INV = [SBOX.index(x) for x in range(16)]
PBOX_INV = [PBOX.index(x) for x in range(128)]

BLOCK_MASK = (1 << BLOCK_SIZE) - 1
KEY_MASK = (1 << KEY_SIZE) - 1
KEY_NIBBLES = 32


def gift_128_128_sbox_layer_acc(state: int, i: int, acc: int) -> int:
    """Recursive accumulator for SubCells (mirrors the Isabelle recursive
    helper gift_128_128_sbox_layer_acc)."""
    if i >= 32:
        return acc
    sboxed = SBOX[(state >> (i * 4)) & 0xF]
    return gift_128_128_sbox_layer_acc(state, i + 1, acc | (sboxed << (i * 4)))


def gift_128_128_sbox_layer(state: int) -> int:
    """Apply the 4-bit S-box (SubCells) to all 32 nibbles of the state."""
    return gift_128_128_sbox_layer_acc(state, 0, 0)


def gift_128_128_sbox_layer_inv_acc(state: int, i: int, acc: int) -> int:
    """Recursive accumulator for the inverse SubCells (mirrors the
    Isabelle recursive helper gift_128_128_sbox_layer_inv_acc)."""
    if i >= 32:
        return acc
    sboxed = SBOX_INV[(state >> (i * 4)) & 0xF]
    return gift_128_128_sbox_layer_inv_acc(state, i + 1, acc | (sboxed << (i * 4)))


def gift_128_128_sbox_layer_inv(state: int) -> int:
    """Inverse SubCells (decryption direction)."""
    return gift_128_128_sbox_layer_inv_acc(state, 0, 0)


def gift_128_128_permutation_layer_acc(state: int, i: int, acc: int) -> int:
    """Recursive accumulator for PermBits (mirrors the Isabelle recursive
    helper gift_128_128_permutation_layer_acc)."""
    if i >= 128:
        return acc
    bit_val = (state >> i) & 0x1
    return gift_128_128_permutation_layer_acc(state, i + 1, acc | (bit_val << PBOX[i]))


def gift_128_128_permutation_layer(state: int) -> int:
    """Bit permutation PermBits: bit i moves to position PBOX[i]."""
    return gift_128_128_permutation_layer_acc(state, 0, 0)


def gift_128_128_permutation_layer_inv_acc(state: int, i: int, acc: int) -> int:
    """Recursive accumulator for the inverse PermBits (mirrors the
    Isabelle recursive helper gift_128_128_permutation_layer_inv_acc)."""
    if i >= 128:
        return acc
    bit_val = (state >> i) & 0x1
    return gift_128_128_permutation_layer_inv_acc(state, i + 1, acc | (bit_val << PBOX_INV[i]))


def gift_128_128_permutation_layer_inv(state: int) -> int:
    """Inverse PermBits (decryption direction)."""
    return gift_128_128_permutation_layer_inv_acc(state, 0, 0)


def gift_128_128_update_key_state(key_nibbles: list[int]) -> list[int]:
    """
    Advance the 32-nibble (128-bit) key state by one key-schedule step:
    rotate the whole register right by 32 bits, then rotate the two
    16-bit words k0 (nibbles 24..27, by 12 bits) and k1 (nibbles 28..31,
    by 2 bits) within themselves. Identical to GIFT-64/128's key schedule.
    """
    temp = [key_nibbles[(i + 8) % KEY_NIBBLES] for i in range(KEY_NIBBLES)]
    new_key = temp[:]

    new_key[24] = temp[27]
    new_key[25] = temp[24]
    new_key[26] = temp[25]
    new_key[27] = temp[26]

    new_key[28] = ((temp[28] & 0xC) >> 2) ^ ((temp[29] & 0x3) << 2)
    new_key[29] = ((temp[29] & 0xC) >> 2) ^ ((temp[30] & 0x3) << 2)
    new_key[30] = ((temp[30] & 0xC) >> 2) ^ ((temp[31] & 0x3) << 2)
    new_key[31] = ((temp[31] & 0xC) >> 2) ^ ((temp[28] & 0x3) << 2)

    return new_key


def gift_128_128_extract_round_key(key_nibbles: list[int]) -> int:
    """
    Pack the round-key XOR mask for AddRoundKey from the current key
    state: U = nibbles[0:8] (32 bits), V = nibbles[16:24] (32 bits);
    bit i of U goes to state bit 4i+1, bit i of V goes to state bit 4i+2.
    """
    u = sum(key_nibbles[k] << (4 * k) for k in range(8))
    v = sum(key_nibbles[16 + k] << (4 * k) for k in range(8))

    mask = 0
    for i in range(32):
        mask |= ((u >> i) & 0x1) << (4 * i + 1)
        mask |= ((v >> i) & 0x1) << (4 * i + 2)
    return mask


def gift_128_128_generate_round_keys(master_key: int) -> list[int]:
    """Generate the 40 round-key XOR masks (one per round) for GIFT-128/128."""
    key_nibbles = [(master_key >> (4 * i)) & 0xF for i in range(KEY_NIBBLES)]
    round_keys = []
    for _ in range(ROUNDS):
        round_keys.append(gift_128_128_extract_round_key(key_nibbles))
        key_nibbles = gift_128_128_update_key_state(key_nibbles)
    return round_keys


def gift_128_128_round_constant_mask(round_index: int) -> int:
    """Compute the AddConstant XOR mask for one round (mirrors the
    Isabelle definition gift_128_128_round_constant_mask)."""
    rc = RC[round_index]
    const_mask = 1 << (BLOCK_SIZE - 1)
    for b in range(6):
        const_mask |= ((rc >> b) & 0x1) << (4 * b + 3)
    return const_mask


def gift_128_128_encrypt_round(state: int, round_key: int, round_index: int) -> int:
    """One GIFT round: SubCells, then PermBits, then AddRoundKey+AddConstant."""
    state = gift_128_128_sbox_layer(state)
    state = gift_128_128_permutation_layer(state)
    state ^= round_key
    state ^= gift_128_128_round_constant_mask(round_index)
    return state & BLOCK_MASK


def gift_128_128_decrypt_round(state: int, round_key: int, round_index: int) -> int:
    """Inverse GIFT round: undo AddRoundKey+AddConstant, then PermBits, then SubCells."""
    state ^= gift_128_128_round_constant_mask(round_index)
    state ^= round_key

    state = gift_128_128_permutation_layer_inv(state)
    state = gift_128_128_sbox_layer_inv(state)
    return state


def gift_128_128_encrypt_rounds_iterate(state: int, round_keys: list[int], i: int) -> int:
    """Recursive encryption iterator over all 40 rounds."""
    if i >= ROUNDS:
        return state
    next_state = gift_128_128_encrypt_round(state, round_keys[i], i)
    return gift_128_128_encrypt_rounds_iterate(next_state, round_keys, i + 1)


def gift_128_128_decrypt_rounds_iterate(state: int, round_keys: list[int], i: int) -> int:
    """Recursive decryption iterator: rounds consumed in reverse (39 down to 0)."""
    if i >= ROUNDS:
        return state
    round_index = ROUNDS - 1 - i
    next_state = gift_128_128_decrypt_round(state, round_keys[round_index], round_index)
    return gift_128_128_decrypt_rounds_iterate(next_state, round_keys, i + 1)


def gift_128_128_encrypt(plaintext: int, master_key: int) -> int:
    """Encrypt one 128-bit block under one 128-bit master key."""
    round_keys = gift_128_128_generate_round_keys(master_key)
    return gift_128_128_encrypt_rounds_iterate(plaintext & BLOCK_MASK, round_keys, 0)


def gift_128_128_decrypt(ciphertext: int, master_key: int) -> int:
    """Decrypt one 128-bit block under one 128-bit master key."""
    round_keys = gift_128_128_generate_round_keys(master_key)
    return gift_128_128_decrypt_rounds_iterate(ciphertext & BLOCK_MASK, round_keys, 0)


def gift_128_128_test() -> bool:
    """Official GIFT-128/128 test vectors (designers' reference implementation)."""
    print("=" * 60)
    print("Testing GIFT-128/128")
    print("=" * 60)

    vectors = [
        (
            0x00000000000000000000000000000000,
            0x00000000000000000000000000000000,
            0xCD0BD738388AD3F668B15A36CEB6FF92,
        ),
        (
            0xFEDCBA9876543210FEDCBA9876543210,
            0xFEDCBA9876543210FEDCBA9876543210,
            0x8422241A6DBF5A9346AF468409EE0152,
        ),
        (
            0xD0F5C59A7700D3E799028FA9F90AD837,
            0xE39C141FA57DBA43F08A85B6A91F86C1,
            0x13EDE67CBDCC3DBF400A62D6977265EA,
        ),
    ]

    all_ok = True
    for idx, (key, pt, expected_ct) in enumerate(vectors, start=1):
        ct = gift_128_128_encrypt(pt, key)
        dec = gift_128_128_decrypt(ct, key)
        ok_enc = ct == expected_ct
        ok_dec = dec == pt
        print(f"Test Vector {idx}:")
        print(f"  Key:        0x{key:032X}")
        print(f"  Plaintext:  0x{pt:032X}")
        print(f"  Ciphertext: 0x{ct:032X}")
        print(f"  Expected:   0x{expected_ct:032X}")
        print(f"  Decrypted:  0x{dec:032X}")
        print("  ✅ PASSED" if (ok_enc and ok_dec) else "  ❌ FAILED")
        all_ok = all_ok and ok_enc and ok_dec

    print()
    print("✅ All GIFT-128/128 tests passed!" if all_ok else "❌ GIFT-128/128 TEST FAILURE")
    print("=" * 60)
    return all_ok


if __name__ == "__main__":
    success = gift_128_128_test()
    if not success:
        raise SystemExit(1)
