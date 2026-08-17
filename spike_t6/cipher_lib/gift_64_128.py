"""
GIFT-64/128 block cipher (single-variant, tiered implementation).

T1: Constants
T2: Primitives (S-box layer, permutation layer, and inverses)
T3: Key schedule
T4: Orchestration (encrypt/decrypt/test)

Reference: Banik, Pandey, Peyrin, Sasaki, Sim, Todo, "GIFT: A Small
Present Towards Reaching the Limit of Lightweight Encryption", CHES 2017
(eprint.iacr.org/2017/622). Round structure, S-box, bit permutation and
key schedule ported from the designers' own reference implementation
(github.com/giftcipher/gift, GIFT64-128_cipher.cpp).
"""


WORD_SIZE = 4
BLOCK_SIZE = 64
KEY_SIZE = 128
ROUNDS = 28

SBOX = [1, 10, 4, 12, 6, 15, 3, 9, 2, 13, 11, 7, 5, 0, 8, 14]

PBOX = [
    0, 17, 34, 51, 48, 1, 18, 35, 32, 49, 2, 19, 16, 33, 50, 3,
    4, 21, 38, 55, 52, 5, 22, 39, 36, 53, 6, 23, 20, 37, 54, 7,
    8, 25, 42, 59, 56, 9, 26, 43, 40, 57, 10, 27, 24, 41, 58, 11,
    12, 29, 46, 63, 60, 13, 30, 47, 44, 61, 14, 31, 28, 45, 62, 15,
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
PBOX_INV = [PBOX.index(x) for x in range(64)]

BLOCK_MASK = (1 << BLOCK_SIZE) - 1
KEY_MASK = (1 << KEY_SIZE) - 1
KEY_NIBBLES = 32


def gift_64_128_sbox_layer_acc(state: int, i: int, acc: int) -> int:
    """Recursive accumulator for SubCells (mirrors the Isabelle recursive
    helper gift_64_128_sbox_layer_acc)."""
    if i >= 16:
        return acc
    sboxed = SBOX[(state >> (i * 4)) & 0xF]
    return gift_64_128_sbox_layer_acc(state, i + 1, acc | (sboxed << (i * 4)))


def gift_64_128_sbox_layer(state: int) -> int:
    """Apply the 4-bit S-box (SubCells) to all 16 nibbles of the state."""
    return gift_64_128_sbox_layer_acc(state, 0, 0)


def gift_64_128_sbox_layer_inv_acc(state: int, i: int, acc: int) -> int:
    """Recursive accumulator for the inverse SubCells (mirrors the
    Isabelle recursive helper gift_64_128_sbox_layer_inv_acc)."""
    if i >= 16:
        return acc
    sboxed = SBOX_INV[(state >> (i * 4)) & 0xF]
    return gift_64_128_sbox_layer_inv_acc(state, i + 1, acc | (sboxed << (i * 4)))


def gift_64_128_sbox_layer_inv(state: int) -> int:
    """Inverse SubCells (decryption direction)."""
    return gift_64_128_sbox_layer_inv_acc(state, 0, 0)


def gift_64_128_permutation_layer_acc(state: int, i: int, acc: int) -> int:
    """Recursive accumulator for PermBits (mirrors the Isabelle recursive
    helper gift_64_128_permutation_layer_acc)."""
    if i >= 64:
        return acc
    bit_val = (state >> i) & 0x1
    return gift_64_128_permutation_layer_acc(state, i + 1, acc | (bit_val << PBOX[i]))


def gift_64_128_permutation_layer(state: int) -> int:
    """Bit permutation PermBits: bit i moves to position PBOX[i]."""
    return gift_64_128_permutation_layer_acc(state, 0, 0)


def gift_64_128_permutation_layer_inv_acc(state: int, i: int, acc: int) -> int:
    """Recursive accumulator for the inverse PermBits (mirrors the
    Isabelle recursive helper gift_64_128_permutation_layer_inv_acc)."""
    if i >= 64:
        return acc
    bit_val = (state >> i) & 0x1
    return gift_64_128_permutation_layer_inv_acc(state, i + 1, acc | (bit_val << PBOX_INV[i]))


def gift_64_128_permutation_layer_inv(state: int) -> int:
    """Inverse PermBits (decryption direction)."""
    return gift_64_128_permutation_layer_inv_acc(state, 0, 0)


def gift_64_128_update_key_state(key_nibbles: list[int]) -> list[int]:
    """
    Advance the 32-nibble (128-bit) key state by one key-schedule step:
    rotate the whole register right by 32 bits, then rotate the two
    16-bit words k0 (nibbles 24..27, by 12 bits) and k1 (nibbles 28..31,
    by 2 bits) within themselves.
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


def gift_64_128_extract_round_key(key_nibbles: list[int]) -> int:
    """
    Pack the round-key XOR mask for AddRoundKey from the current key
    state: U = nibbles[0:4] (16 bits), V = nibbles[4:8] (16 bits);
    bit i of U goes to state bit 4i, bit i of V goes to state bit 4i+1.
    """
    u = sum(key_nibbles[k] << (4 * k) for k in range(4))
    v = sum(key_nibbles[4 + k] << (4 * k) for k in range(4))

    mask = 0
    for i in range(16):
        mask |= ((u >> i) & 0x1) << (4 * i)
        mask |= ((v >> i) & 0x1) << (4 * i + 1)
    return mask


def gift_64_128_generate_round_keys(master_key: int) -> list[int]:
    """Generate the 28 round-key XOR masks (one per round) for GIFT-64/128."""
    key_nibbles = [(master_key >> (4 * i)) & 0xF for i in range(KEY_NIBBLES)]
    round_keys = []
    for _ in range(ROUNDS):
        round_keys.append(gift_64_128_extract_round_key(key_nibbles))
        key_nibbles = gift_64_128_update_key_state(key_nibbles)
    return round_keys


def gift_64_128_round_constant_mask(round_index: int) -> int:
    """Compute the AddConstant XOR mask for one round (mirrors the
    Isabelle definition gift_64_128_round_constant_mask)."""
    rc = RC[round_index]
    const_mask = 1 << (BLOCK_SIZE - 1)
    for b in range(6):
        const_mask |= ((rc >> b) & 0x1) << (4 * b + 3)
    return const_mask


def gift_64_128_encrypt_round(state: int, round_key: int, round_index: int) -> int:
    """One GIFT round: SubCells, then PermBits, then AddRoundKey+AddConstant."""
    state = gift_64_128_sbox_layer(state)
    state = gift_64_128_permutation_layer(state)
    state ^= round_key
    state ^= gift_64_128_round_constant_mask(round_index)
    return state & BLOCK_MASK


def gift_64_128_decrypt_round(state: int, round_key: int, round_index: int) -> int:
    """Inverse GIFT round: undo AddRoundKey+AddConstant, then PermBits, then SubCells."""
    state ^= gift_64_128_round_constant_mask(round_index)
    state ^= round_key

    state = gift_64_128_permutation_layer_inv(state)
    state = gift_64_128_sbox_layer_inv(state)
    return state


def gift_64_128_encrypt_rounds_iterate(state: int, round_keys: list[int], i: int) -> int:
    """Recursive encryption iterator over all 28 rounds."""
    if i >= ROUNDS:
        return state
    next_state = gift_64_128_encrypt_round(state, round_keys[i], i)
    return gift_64_128_encrypt_rounds_iterate(next_state, round_keys, i + 1)


def gift_64_128_decrypt_rounds_iterate(state: int, round_keys: list[int], i: int) -> int:
    """Recursive decryption iterator: rounds consumed in reverse (27 down to 0)."""
    if i >= ROUNDS:
        return state
    round_index = ROUNDS - 1 - i
    next_state = gift_64_128_decrypt_round(state, round_keys[round_index], round_index)
    return gift_64_128_decrypt_rounds_iterate(next_state, round_keys, i + 1)


def gift_64_128_encrypt(plaintext: int, master_key: int) -> int:
    """Encrypt one 64-bit block under one 128-bit master key."""
    round_keys = gift_64_128_generate_round_keys(master_key)
    return gift_64_128_encrypt_rounds_iterate(plaintext & BLOCK_MASK, round_keys, 0)


def gift_64_128_decrypt(ciphertext: int, master_key: int) -> int:
    """Decrypt one 64-bit block under one 128-bit master key."""
    round_keys = gift_64_128_generate_round_keys(master_key)
    return gift_64_128_decrypt_rounds_iterate(ciphertext & BLOCK_MASK, round_keys, 0)


def gift_64_128_test() -> bool:
    """Official GIFT-64/128 test vectors (designers' reference implementation)."""
    print("=" * 60)
    print("Testing GIFT-64/128")
    print("=" * 60)

    vectors = [
        (0x00000000000000000000000000000000, 0x0000000000000000, 0xF62BC3EF34F775AC),
        (0xFEDCBA9876543210FEDCBA9876543210, 0xFEDCBA9876543210, 0xC1B71F66160FF587),
        (0xBD91731EB6BC2713A1F9F6FFC75044E7, 0xC450C7727A9B8A7D, 0xE3272885FA94BA8B),
    ]

    all_ok = True
    for idx, (key, pt, expected_ct) in enumerate(vectors, start=1):
        ct = gift_64_128_encrypt(pt, key)
        dec = gift_64_128_decrypt(ct, key)
        ok_enc = ct == expected_ct
        ok_dec = dec == pt
        print(f"Test Vector {idx}:")
        print(f"  Key:        0x{key:032X}")
        print(f"  Plaintext:  0x{pt:016X}")
        print(f"  Ciphertext: 0x{ct:016X}")
        print(f"  Expected:   0x{expected_ct:016X}")
        print(f"  Decrypted:  0x{dec:016X}")
        print("  ✅ PASSED" if (ok_enc and ok_dec) else "  ❌ FAILED")
        all_ok = all_ok and ok_enc and ok_dec

    print()
    print("✅ All GIFT-64/128 tests passed!" if all_ok else "❌ GIFT-64/128 TEST FAILURE")
    print("=" * 60)
    return all_ok


if __name__ == "__main__":
    success = gift_64_128_test()
    if not success:
        raise SystemExit(1)
