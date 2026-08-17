"""
SKINNY-128/128 block cipher (single-variant, tiered implementation).
Tweakey type TK1 (key size = block size), 8-bit cells.

T1: Constants
T2: Primitives (SubCells layer, ShiftRows, MixColumns)
T3: Tweakey schedule
T4: Orchestration (encrypt/decrypt/test)

Reference: Beierle, Jean, Kolbl, Leander, Moradi, Peyrin, Sasaki,
Sasdrich, Sim, "The SKINNY Family of Block Ciphers and Its Low-Latency
Variant MANTIS", CRYPTO 2016 (eprint.iacr.org/2016/660). Algorithm
cross-validated against two independent third-party implementations
(inmcm/skinny_cipher and CRYPTO-2016-co-author Stefan Kolbl's own
kste/skinny-rs), whose official test vectors agree exactly. TK1 has a
single tweakey component, so no LFSR is ever applied in the schedule.
"""


CELL_BITS = 8
CELL_MASK = 0xFF
BLOCK_SIZE = 128
KEY_SIZE = 128
ROUNDS = 40
TWEAKEY_BLOCKS = 1

SBOX = [
    101, 76, 106, 66, 75, 99, 67, 107, 85, 117, 90, 122, 83, 115, 91, 123,
    53, 140, 58, 129, 137, 51, 128, 59, 149, 37, 152, 42, 144, 35, 153, 43,
    229, 204, 232, 193, 201, 224, 192, 233, 213, 245, 216, 248, 208, 240, 217, 249,
    165, 28, 168, 18, 27, 160, 19, 169, 5, 181, 10, 184, 3, 176, 11, 185,
    50, 136, 60, 133, 141, 52, 132, 61, 145, 34, 156, 44, 148, 36, 157, 45,
    98, 74, 108, 69, 77, 100, 68, 109, 82, 114, 92, 124, 84, 116, 93, 125,
    161, 26, 172, 21, 29, 164, 20, 173, 2, 177, 12, 188, 4, 180, 13, 189,
    225, 200, 236, 197, 205, 228, 196, 237, 209, 241, 220, 252, 212, 244, 221, 253,
    54, 142, 56, 130, 139, 48, 131, 57, 150, 38, 154, 40, 147, 32, 155, 41,
    102, 78, 104, 65, 73, 96, 64, 105, 86, 118, 88, 120, 80, 112, 89, 121,
    166, 30, 170, 17, 25, 163, 16, 171, 6, 182, 8, 186, 0, 179, 9, 187,
    230, 206, 234, 194, 203, 227, 195, 235, 214, 246, 218, 250, 211, 243, 219, 251,
    49, 138, 62, 134, 143, 55, 135, 63, 146, 33, 158, 46, 151, 39, 159, 47,
    97, 72, 110, 70, 79, 103, 71, 111, 81, 113, 94, 126, 87, 119, 95, 127,
    162, 24, 174, 22, 31, 167, 23, 175, 1, 178, 14, 190, 7, 183, 15, 191,
    226, 202, 238, 198, 207, 231, 199, 239, 210, 242, 222, 254, 215, 247, 223, 255,
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

# Derived lookup table (not independently specified by the cipher).
SBOX_INV = [SBOX.index(x) for x in range(256)]

BLOCK_MASK = (1 << BLOCK_SIZE) - 1
KEY_MASK = (1 << KEY_SIZE) - 1


def skinny_128_128_sub_cells(state: list[int]) -> list[int]:
    """SubCells: apply the 8-bit S-box to every cell of the 4x4 state."""
    return [SBOX[cell] for cell in state]


def skinny_128_128_sub_cells_inv(state: list[int]) -> list[int]:
    """Inverse SubCells (decryption direction)."""
    return [SBOX_INV[cell] for cell in state]


def skinny_128_128_shift_rows(state: list[int]) -> list[int]:
    """ShiftRows: row r (0-indexed) is right-rotated by r cell positions."""
    r0 = state[0:4]
    r1 = state[4:8]
    r2 = state[8:12]
    r3 = state[12:16]
    new_r1 = [r1[3], r1[0], r1[1], r1[2]]
    new_r2 = [r2[2], r2[3], r2[0], r2[1]]
    new_r3 = [r3[1], r3[2], r3[3], r3[0]]
    return r0 + new_r1 + new_r2 + new_r3


def skinny_128_128_shift_rows_inv(state: list[int]) -> list[int]:
    """Inverse ShiftRows (decryption direction)."""
    r0 = state[0:4]
    r1 = state[4:8]
    r2 = state[8:12]
    r3 = state[12:16]
    new_r1 = [r1[1], r1[2], r1[3], r1[0]]
    new_r2 = [r2[2], r2[3], r2[0], r2[1]]
    new_r3 = [r3[3], r3[0], r3[1], r3[2]]
    return r0 + new_r1 + new_r2 + new_r3


def skinny_128_128_mix_columns(state: list[int]) -> list[int]:
    """MixColumns: near-MDS matrix mixing the 4 rows, column-wise (cell-wise)."""
    r0 = state[0:4]
    r1 = state[4:8]
    r2 = state[8:12]
    r3 = state[12:16]
    new_r0 = [a ^ b ^ c for a, b, c in zip(r0, r2, r3)]
    new_r1 = r0
    new_r2 = [a ^ b for a, b in zip(r1, r2)]
    new_r3 = [a ^ b for a, b in zip(r0, r2)]
    return new_r0 + new_r1 + new_r2 + new_r3


def skinny_128_128_mix_columns_inv(state: list[int]) -> list[int]:
    """Inverse MixColumns (decryption direction)."""
    r0 = state[0:4]
    r1 = state[4:8]
    r2 = state[8:12]
    r3 = state[12:16]
    new_r0 = r1
    new_r2 = [a ^ b for a, b in zip(r1, r3)]
    new_r1 = [a ^ b for a, b in zip(r2, new_r2)]
    new_r3 = [a ^ b for a, b in zip(r0, r3)]
    return new_r0 + new_r1 + new_r2 + new_r3


def skinny_128_128_block_to_state(block: int) -> list[int]:
    """Convert a 128-bit integer block to 16 row-major 8-bit cells."""
    return [(block >> (BLOCK_SIZE - CELL_BITS * (i + 1))) & CELL_MASK for i in range(16)]


def skinny_128_128_state_to_block(state: list[int]) -> int:
    """Convert 16 row-major 8-bit cells back to a 128-bit integer block."""
    result = 0
    for cell in state:
        result = (result << CELL_BITS) | cell
    return result


def skinny_128_128_key_to_tweakey_state(master_key: int) -> list[list[int]]:
    """Split the 128-bit key into TWEAKEY_BLOCKS=1 16-cell tweakey array."""
    return [
        skinny_128_128_block_to_state((master_key >> (BLOCK_SIZE * (TWEAKEY_BLOCKS - 1 - z))) & BLOCK_MASK)
        for z in range(TWEAKEY_BLOCKS)
    ]


def skinny_128_128_update_tweakey_state(tweakey_state: list[list[int]]) -> tuple[list[list[int]], list[int]]:
    """
    Advance the single tweakey component by one round: apply the fixed
    cell permutation PT (new rows 0,1 come from old rows 2,3; old rows
    0,1 shift down to become new rows 2,3); no LFSR for TK1. Returns the
    XOR material (rows 0,1, 8 cells) used for this round's AddRoundTweakey.
    """
    new_state = []
    round_key_material = [0] * 8
    for twky in tweakey_state:
        row2 = twky[8:12]
        row3 = twky[12:16]
        perm_row0 = [row2[1], row3[3], row2[0], row3[1]]
        perm_row1 = [row2[2], row3[2], row3[0], row2[3]]

        round_key_material = [a ^ b for a, b in zip(round_key_material, perm_row0 + perm_row1)]
        new_state.append(perm_row0 + perm_row1 + twky[0:4] + twky[4:8])

    return new_state, round_key_material


def skinny_128_128_initial_round_key(tweakey_state: list[list[int]]) -> list[int]:
    """Initial round-key XOR material: fold XOR of rows 0,1 across all
    tweakey components (mirrors the Isabelle definition
    skinny_128_128_initial_round_key)."""
    acc = [0] * 8
    for twky in tweakey_state:
        acc = [a ^ b for a, b in zip(acc, twky[0:4] + twky[4:8])]
    return acc


def skinny_128_128_generate_round_tweakeys_acc(
    tweakey_state: list[list[int]], round_index: int, acc: list[list[int]]
) -> list[list[int]]:
    """Recursive accumulator for the round-tweakey schedule (mirrors the
    Isabelle recursive helper skinny_128_128_generate_round_tweakeys_acc)."""
    if round_index >= ROUNDS - 1:
        return acc
    new_state, rkm = skinny_128_128_update_tweakey_state(tweakey_state)
    return skinny_128_128_generate_round_tweakeys_acc(new_state, round_index + 1, acc + [rkm])


def skinny_128_128_generate_round_tweakeys(master_key: int) -> list[list[int]]:
    """Generate the round-key XOR material (8 cells: rows 0,1) for all ROUNDS rounds."""
    tweakey_state = skinny_128_128_key_to_tweakey_state(master_key)
    rk0 = skinny_128_128_initial_round_key(tweakey_state)
    return skinny_128_128_generate_round_tweakeys_acc(tweakey_state, 0, [rk0])


def skinny_128_128_encrypt_round(state: list[int], round_index: int, round_key_material: list[int]) -> list[int]:
    """One SKINNY round: SubCells, AddConstants, AddRoundTweakey, ShiftRows, MixColumns."""
    state = skinny_128_128_sub_cells(state)

    rc = RC[round_index % len(RC)]
    state = state[:]
    state[0] ^= rc & 0xF
    state[4] ^= (rc >> 4) & 0x3
    state[8] ^= 0x2

    for i in range(8):
        state[i] ^= round_key_material[i]

    state = skinny_128_128_shift_rows(state)
    state = skinny_128_128_mix_columns(state)
    return state


def skinny_128_128_decrypt_round(state: list[int], round_index: int, round_key_material: list[int]) -> list[int]:
    """Inverse SKINNY round (decryption direction)."""
    state = skinny_128_128_mix_columns_inv(state)
    state = skinny_128_128_shift_rows_inv(state)

    state = state[:]
    for i in range(8):
        state[i] ^= round_key_material[i]

    rc = RC[round_index % len(RC)]
    state[0] ^= rc & 0xF
    state[4] ^= (rc >> 4) & 0x3
    state[8] ^= 0x2

    state = skinny_128_128_sub_cells_inv(state)
    return state


def skinny_128_128_encrypt_rounds_iterate(state: list[int], round_keys: list[list[int]], i: int) -> list[int]:
    """Recursive encryption iterator over all ROUNDS rounds."""
    if i >= ROUNDS:
        return state
    next_state = skinny_128_128_encrypt_round(state, i, round_keys[i])
    return skinny_128_128_encrypt_rounds_iterate(next_state, round_keys, i + 1)


def skinny_128_128_decrypt_rounds_iterate(state: list[int], round_keys: list[list[int]], i: int) -> list[int]:
    """Recursive decryption iterator: rounds consumed ROUNDS-1 down to 0."""
    if i >= ROUNDS:
        return state
    round_index = ROUNDS - 1 - i
    next_state = skinny_128_128_decrypt_round(state, round_index, round_keys[round_index])
    return skinny_128_128_decrypt_rounds_iterate(next_state, round_keys, i + 1)


def skinny_128_128_encrypt(plaintext: int, master_key: int) -> int:
    """Encrypt one 128-bit block under one 128-bit tweakey."""
    round_keys = skinny_128_128_generate_round_tweakeys(master_key)
    state = skinny_128_128_block_to_state(plaintext & BLOCK_MASK)
    state = skinny_128_128_encrypt_rounds_iterate(state, round_keys, 0)
    return skinny_128_128_state_to_block(state)


def skinny_128_128_decrypt(ciphertext: int, master_key: int) -> int:
    """Decrypt one 128-bit block under one 128-bit tweakey."""
    round_keys = skinny_128_128_generate_round_tweakeys(master_key)
    state = skinny_128_128_block_to_state(ciphertext & BLOCK_MASK)
    state = skinny_128_128_decrypt_rounds_iterate(state, round_keys, 0)
    return skinny_128_128_state_to_block(state)


def skinny_128_128_test() -> bool:
    """Official SKINNY-128/128 test vector (cross-validated against two independent implementations)."""
    print("=" * 60)
    print("Testing SKINNY-128/128")
    print("=" * 60)

    vectors = [
        (
            0x4F55CFB0520CAC52FD92C15F37073E93,
            0xF20ADB0EB08B648A3B2EEED1F0ADDA14,
            0x22FF30D498EA62D7E45B476E33675B74,
        ),
        (
            0x17401096D712B2ADCC0143A91DDDB11C,
            0x5768DE09FD1F69FD2A90DE397270597A,
            0x1DE2136FB373E0522CC2351306E9F62D,
        ),
    ]

    all_ok = True
    for idx, (key, pt, expected_ct) in enumerate(vectors, start=1):
        ct = skinny_128_128_encrypt(pt, key)
        dec = skinny_128_128_decrypt(ct, key)
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
    print("✅ All SKINNY-128/128 tests passed!" if all_ok else "❌ SKINNY-128/128 TEST FAILURE")
    print("=" * 60)
    return all_ok


if __name__ == "__main__":
    success = skinny_128_128_test()
    if not success:
        raise SystemExit(1)
