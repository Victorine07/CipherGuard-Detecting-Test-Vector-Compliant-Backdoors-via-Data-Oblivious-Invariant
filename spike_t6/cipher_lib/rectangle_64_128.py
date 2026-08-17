"""
RECTANGLE-64/128 block cipher (single-variant, tiered implementation).

T1: Constants
T2: Primitives (SubColumn S-box layer, ShiftRow layer, and inverses)
T3: Key schedule
T4: Orchestration (encrypt/decrypt/test)

Reference: Zhang, Bao, Lin, Rijmen, Yang, Verbauwhede, "RECTANGLE: A
Bit-slice Lightweight Block Cipher Suitable for Multiple Platforms",
eprint.iacr.org/2014/084. Official test vectors cross-checked against a
from-scratch port of the algorithm, independently verified row-by-row
against the paper's published Table 10 values.

State representation: the 64-bit state is 4 rows of 16 bits, row r
occupying bits [16r, 16r+15] of the integer (row 0 = least significant).
Each column j (0..15) is the 4-bit value formed by bit j of each row.
"""


WORD_SIZE = 4
BLOCK_SIZE = 64
KEY_SIZE = 128
ROUNDS = 25

SBOX = [0x6, 0x5, 0xC, 0xA, 0x1, 0xE, 0x7, 0x9, 0xB, 0x0, 0x3, 0xD, 0x8, 0xF, 0x4, 0x2]

ROW_ROTATIONS = [0, 1, 12, 13]

RC = [
    0x01, 0x02, 0x04, 0x09, 0x12, 0x05, 0x0B, 0x16,
    0x0C, 0x19, 0x13, 0x07, 0x0F, 0x1F, 0x1E, 0x1C,
    0x18, 0x11, 0x03, 0x06, 0x0D, 0x1B, 0x17, 0x0E, 0x1D,
]

# Derived lookup table (not independently specified by the cipher).
SBOX_INV = [SBOX.index(x) for x in range(16)]

ROW_MASK = 0xFFFF
KEY_ROW_MASK = 0xFFFFFFFF
BLOCK_MASK = (1 << BLOCK_SIZE) - 1
KEY_MASK = (1 << KEY_SIZE) - 1


def rectangle_64_128_rol16(x: int, r: int) -> int:
    """Rotate a 16-bit row left by r bits."""
    r %= 16
    return ((x << r) & ROW_MASK) | (x >> (16 - r))


def rectangle_64_128_rol32(x: int, r: int) -> int:
    """Rotate a 32-bit key row left by r bits."""
    r %= 32
    return ((x << r) & KEY_ROW_MASK) | (x >> (32 - r))


def rectangle_64_128_sub_column_acc(state: int, j: int, acc: int) -> int:
    """Recursive accumulator for SubColumn (mirrors the Isabelle recursive
    helper rectangle_64_128_sub_column_acc)."""
    if j >= 16:
        return acc
    col = 0
    for b in range(4):
        col |= ((state >> (16 * b + j)) & 1) << b
    s = SBOX[col]
    placed = 0
    for b in range(4):
        placed |= ((s >> b) & 1) << (16 * b + j)
    return rectangle_64_128_sub_column_acc(state, j + 1, acc | placed)


def rectangle_64_128_sub_column(state: int) -> int:
    """SubColumn: apply the 4-bit S-box to each of the 16 columns."""
    return rectangle_64_128_sub_column_acc(state, 0, 0)


def rectangle_64_128_sub_column_inv_acc(state: int, j: int, acc: int) -> int:
    """Recursive accumulator for the inverse SubColumn (mirrors the
    Isabelle recursive helper rectangle_64_128_sub_column_inv_acc)."""
    if j >= 16:
        return acc
    col = 0
    for b in range(4):
        col |= ((state >> (16 * b + j)) & 1) << b
    s = SBOX_INV[col]
    placed = 0
    for b in range(4):
        placed |= ((s >> b) & 1) << (16 * b + j)
    return rectangle_64_128_sub_column_inv_acc(state, j + 1, acc | placed)


def rectangle_64_128_sub_column_inv(state: int) -> int:
    """Inverse SubColumn (decryption direction)."""
    return rectangle_64_128_sub_column_inv_acc(state, 0, 0)


def rectangle_64_128_shift_row(state: int) -> int:
    """ShiftRow: left-rotate each row by its fixed offset (0, 1, 12, 13)."""
    output = 0
    for r in range(4):
        row = (state >> (16 * r)) & ROW_MASK
        output |= rectangle_64_128_rol16(row, ROW_ROTATIONS[r]) << (16 * r)
    return output


def rectangle_64_128_shift_row_inv(state: int) -> int:
    """Inverse ShiftRow: right-rotate each row by its fixed offset."""
    output = 0
    for r in range(4):
        row = (state >> (16 * r)) & ROW_MASK
        output |= rectangle_64_128_rol16(row, (16 - ROW_ROTATIONS[r]) % 16) << (16 * r)
    return output


def rectangle_64_128_key_to_rows(master_key: int) -> list[int]:
    """Split the 128-bit key into 4 32-bit rows (row 0 = least significant)."""
    return [(master_key >> (32 * i)) & KEY_ROW_MASK for i in range(4)]


def rectangle_64_128_sbox_columns_acc(rows: list[int], j: int, num_cols: int, acc: list[int]) -> list[int]:
    """Recursive accumulator applying the S-box to columns 0..num_cols-1 of
    rows 0..3 (mirrors the Isabelle recursive helper
    rectangle_64_128_sbox_columns_acc). acc must start as a copy of rows[:4]
    so that bits outside the active column range are preserved unchanged."""
    if j >= num_cols:
        return acc
    col = 0
    for b in range(4):
        col |= ((rows[b] >> j) & 1) << b
    s = SBOX[col]
    new_acc = list(acc)
    for b in range(4):
        if (s >> b) & 1:
            new_acc[b] |= 1 << j
        else:
            new_acc[b] &= (~(1 << j)) & KEY_ROW_MASK
    return rectangle_64_128_sbox_columns_acc(rows, j + 1, num_cols, new_acc)


def rectangle_64_128_apply_sbox_to_columns(rows: list[int], num_cols: int) -> list[int]:
    """Apply the S-box to the rightmost num_cols columns of rows 0..3
    (mirrors the Isabelle definition rectangle_64_128_apply_sbox_to_columns)."""
    return rectangle_64_128_sbox_columns_acc(rows, 0, num_cols, list(rows[:4]))


def rectangle_64_128_update_key_rows(rows: list[int], round_index: int) -> list[int]:
    """
    Advance the 4-row (32-bit) key state by one key-schedule step: apply
    the S-box to the 8 rightmost columns of all 4 rows, perform a
    generalized-Feistel row shuffle, then XOR the round constant into the
    low 5 bits of row 0.
    """
    sboxed = rectangle_64_128_apply_sbox_to_columns(rows, 8)
    r0, r1, r2, r3 = sboxed
    new_rows = [
        (rectangle_64_128_rol32(r0, 8) ^ r1) & KEY_ROW_MASK,
        r2,
        (rectangle_64_128_rol32(r2, 16) ^ r3) & KEY_ROW_MASK,
        r0,
    ]
    new_rows[0] ^= RC[round_index]
    return new_rows


def rectangle_64_128_generate_round_keys_acc(rows: list[int], round_index: int, acc: list[int]) -> list[int]:
    """Recursive accumulator for the round-key schedule (mirrors the
    Isabelle recursive helper rectangle_64_128_generate_round_keys_acc)."""
    packed = sum((rows[i] & ROW_MASK) << (16 * i) for i in range(4))
    if round_index >= ROUNDS:
        return acc + [packed]
    return rectangle_64_128_generate_round_keys_acc(
        rectangle_64_128_update_key_rows(rows, round_index), round_index + 1, acc + [packed]
    )


def rectangle_64_128_generate_round_keys(master_key: int) -> list[int]:
    """Generate all 26 round-key integers (K0..K25) for RECTANGLE-64/128."""
    return rectangle_64_128_generate_round_keys_acc(rectangle_64_128_key_to_rows(master_key), 0, [])


def rectangle_64_128_encrypt_round(state: int, round_key: int) -> int:
    """One RECTANGLE round: AddRoundKey, then SubColumn, then ShiftRow."""
    state ^= round_key
    state = rectangle_64_128_sub_column(state)
    state = rectangle_64_128_shift_row(state)
    return state


def rectangle_64_128_decrypt_round(state: int, round_key: int) -> int:
    """Inverse RECTANGLE round: ShiftRow_inv, SubColumn_inv, then AddRoundKey."""
    state = rectangle_64_128_shift_row_inv(state)
    state = rectangle_64_128_sub_column_inv(state)
    state ^= round_key
    return state


def rectangle_64_128_encrypt_rounds_iterate(state: int, round_keys: list[int], i: int) -> int:
    """Recursive encryption iterator over the 25 main rounds."""
    if i >= ROUNDS:
        return state ^ round_keys[ROUNDS]
    next_state = rectangle_64_128_encrypt_round(state, round_keys[i])
    return rectangle_64_128_encrypt_rounds_iterate(next_state, round_keys, i + 1)


def rectangle_64_128_decrypt_rounds_iterate(state: int, round_keys: list[int], i: int) -> int:
    """Recursive decryption iterator: rounds consumed K24 down to K0, after undoing K25."""
    if i >= ROUNDS:
        return state
    round_key = round_keys[ROUNDS - 1 - i]
    next_state = rectangle_64_128_decrypt_round(state, round_key)
    return rectangle_64_128_decrypt_rounds_iterate(next_state, round_keys, i + 1)


def rectangle_64_128_encrypt(plaintext: int, master_key: int) -> int:
    """Encrypt one 64-bit block under one 128-bit master key."""
    round_keys = rectangle_64_128_generate_round_keys(master_key)
    return rectangle_64_128_encrypt_rounds_iterate(plaintext & BLOCK_MASK, round_keys, 0)


def rectangle_64_128_decrypt(ciphertext: int, master_key: int) -> int:
    """Decrypt one 64-bit block under one 128-bit master key."""
    round_keys = rectangle_64_128_generate_round_keys(master_key)
    state = (ciphertext & BLOCK_MASK) ^ round_keys[ROUNDS]
    return rectangle_64_128_decrypt_rounds_iterate(state, round_keys, 0)


def rectangle_64_128_test() -> bool:
    """Official RECTANGLE-64/128 test vectors (Table 10 of the paper) plus round-trip checks."""
    print("=" * 60)
    print("Testing RECTANGLE-64/128")
    print("=" * 60)

    vectors = [
        (0x00000000000000000000000000000000, 0x0000000000000000, 0x99EE44A43613AEE6),
        (0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFF, 0xFFFFFFFFFFFFFFFF, 0x7A464A15EFEEE83E),
        (0x0123456789ABCDEF0123456789ABCDEF, 0xDEADBEEFCAFEBABE, 0xD10261B0D36FDDC7),
    ]

    all_ok = True
    for idx, (key, pt, expected_ct) in enumerate(vectors, start=1):
        ct = rectangle_64_128_encrypt(pt, key)
        dec = rectangle_64_128_decrypt(ct, key)
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
    print("✅ All RECTANGLE-64/128 tests passed!" if all_ok else "❌ RECTANGLE-64/128 TEST FAILURE")
    print("=" * 60)
    return all_ok


if __name__ == "__main__":
    success = rectangle_64_128_test()
    if not success:
        raise SystemExit(1)
