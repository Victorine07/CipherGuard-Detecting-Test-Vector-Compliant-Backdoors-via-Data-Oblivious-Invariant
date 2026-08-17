"""
LEA-128/192 Block Cipher
========================
Reference implementation matching the official LEA equations and the
Isabelle/HOL formalization in thy ciphers/lea_128_192.thy.

T1: Constants
T2: Primitives (rotations, single-round encrypt/decrypt transform)
T3: Structural Components (key schedule)
T4: Orchestration (block/word conversion, round iteration, encrypt/decrypt)

Variant: LEA-128/192 -- 128-bit block, 192-bit key, 28 rounds, 6 key words.
"""


LEA_128_192_BLOCK_WORDS = 4
LEA_128_192_KEY_WORDS = 6
LEA_128_192_ROUNDS = 28
LEA_128_192_WORD_SIZE = 32
LEA_128_192_MOD_MASK = 0xFFFFFFFF

LEA_128_192_DELTA = [
    0xC3EFE9DB,
    0x44626B02,
    0x79E27C8A,
    0x78DF30EC,
    0x715EA49E,
    0xC785DA0A,
    0xE04EF22A,
    0xE5C40957,
]


def lea_128_192_rol(x: int, n: int) -> int:
    n %= LEA_128_192_WORD_SIZE
    return ((x << n) | (x >> (LEA_128_192_WORD_SIZE - n))) & LEA_128_192_MOD_MASK


def lea_128_192_ror(x: int, n: int) -> int:
    n %= LEA_128_192_WORD_SIZE
    return ((x >> n) | (x << (LEA_128_192_WORD_SIZE - n))) & LEA_128_192_MOD_MASK


def lea_128_192_encrypt_round(state: list[int], rk: list[int]) -> list[int]:
    x0, x1, x2, x3 = state
    k0, k1, k2, k3, k4, k5 = rk

    y0 = lea_128_192_rol(((x0 ^ k0) + (x1 ^ k1)) & LEA_128_192_MOD_MASK, 9)
    y1 = lea_128_192_ror(((x1 ^ k2) + (x2 ^ k3)) & LEA_128_192_MOD_MASK, 5)
    y2 = lea_128_192_ror(((x2 ^ k4) + (x3 ^ k5)) & LEA_128_192_MOD_MASK, 3)
    y3 = x0

    return [y0, y1, y2, y3]


def lea_128_192_decrypt_round(state: list[int], rk: list[int]) -> list[int]:
    y0, y1, y2, y3 = state
    k0, k1, k2, k3, k4, k5 = rk

    x0 = y3
    x1 = ((lea_128_192_ror(y0, 9) - (x0 ^ k0)) & LEA_128_192_MOD_MASK) ^ k1
    x2 = ((lea_128_192_rol(y1, 5) - (x1 ^ k2)) & LEA_128_192_MOD_MASK) ^ k3
    x3 = ((lea_128_192_rol(y2, 3) - (x2 ^ k4)) & LEA_128_192_MOD_MASK) ^ k5

    return [x0, x1, x2, x3]


def lea_128_192_extract_key_words(master_key: int) -> list[int]:
    return [(master_key >> (32 * i)) & LEA_128_192_MOD_MASK for i in range(LEA_128_192_KEY_WORDS)]


def lea_128_192_step_key_expansion(T: list[int], i: int) -> tuple[list[int], list[int]]:
    d = LEA_128_192_DELTA[i % 6]

    t0 = lea_128_192_rol((T[0] + lea_128_192_rol(d, i)) & LEA_128_192_MOD_MASK, 1)
    t1 = lea_128_192_rol((T[1] + lea_128_192_rol(d, i + 1)) & LEA_128_192_MOD_MASK, 3)
    t2 = lea_128_192_rol((T[2] + lea_128_192_rol(d, i + 2)) & LEA_128_192_MOD_MASK, 6)
    t3 = lea_128_192_rol((T[3] + lea_128_192_rol(d, i + 3)) & LEA_128_192_MOD_MASK, 11)
    t4 = lea_128_192_rol((T[4] + lea_128_192_rol(d, i + 4)) & LEA_128_192_MOD_MASK, 13)
    t5 = lea_128_192_rol((T[5] + lea_128_192_rol(d, i + 5)) & LEA_128_192_MOD_MASK, 17)

    next_T = [t0, t1, t2, t3, t4, t5]
    rk = [t0, t1, t2, t3, t4, t5]
    return rk, next_T


def lea_128_192_gen_round_keys_iter(T: list[int], i: int, acc: list[list[int]]) -> list[list[int]]:
    """Recursive round-key accumulator (mirrors the Isabelle recursive
    helper lea_128_192_gen_round_keys_iter)."""
    if i >= LEA_128_192_ROUNDS:
        return acc
    rk, T_next = lea_128_192_step_key_expansion(T, i)
    return lea_128_192_gen_round_keys_iter(T_next, i + 1, acc + [rk])


def lea_128_192_generate_round_keys(master_key: int) -> list[list[int]]:
    T = lea_128_192_extract_key_words(master_key)
    return lea_128_192_gen_round_keys_iter(T, 0, [])


def lea_128_192_block_to_words(block: int) -> list[int]:
    return [(block >> (32 * i)) & LEA_128_192_MOD_MASK for i in range(4)]


def lea_128_192_words_to_block(words: list[int]) -> int:
    return sum((w & LEA_128_192_MOD_MASK) << (32 * i) for i, w in enumerate(words))


def lea_128_192_encrypt_iter(state: list[int], round_keys: list[list[int]]) -> list[int]:
    """Recursively apply encrypt_round over the round-key list (mirrors
    the Isabelle pattern-matching recursion in lea_128_192_encrypt_iter)."""
    if not round_keys:
        return state
    return lea_128_192_encrypt_iter(lea_128_192_encrypt_round(state, round_keys[0]), round_keys[1:])


def lea_128_192_decrypt_iter(state: list[int], round_keys: list[list[int]]) -> list[int]:
    for rk in reversed(round_keys):
        state = lea_128_192_decrypt_round(state, rk)
    return state


def lea_128_192_encrypt_block(plaintext: int, round_keys: list[list[int]]) -> int:
    state = lea_128_192_block_to_words(plaintext)
    out_state = lea_128_192_encrypt_iter(state, round_keys)
    return lea_128_192_words_to_block(out_state)


def lea_128_192_decrypt_block(ciphertext: int, round_keys: list[list[int]]) -> int:
    state = lea_128_192_block_to_words(ciphertext)
    out_state = lea_128_192_decrypt_iter(state, round_keys)
    return lea_128_192_words_to_block(out_state)


def lea_128_192_encrypt(plaintext: int, master_key: int) -> int:
    round_keys = lea_128_192_generate_round_keys(master_key)
    return lea_128_192_encrypt_block(plaintext, round_keys)


def lea_128_192_decrypt(ciphertext: int, master_key: int) -> int:
    round_keys = lea_128_192_generate_round_keys(master_key)
    return lea_128_192_decrypt_block(ciphertext, round_keys)


def test_lea_128_192() -> bool:
    """No official test vector was available when this file was authored;
    correctness is checked via encrypt/decrypt round-trip self-consistency
    (matching the established pattern used by several Speck variants
    without a sourced vector)."""
    print("=" * 60)
    print("Testing LEA-128/192")
    print("=" * 60)

    print("  No official test vector available for LEA-128/192")
    print("  Testing round-trip only...")

    plaintext = 0x101112131415161718191A1B1C1D1E1F
    master_key = 0x0F1E2D3C4B5A69788796A5B4C3D2E1F00102030405060708

    ciphertext = lea_128_192_encrypt(plaintext, master_key)
    decrypted = lea_128_192_decrypt(ciphertext, master_key)

    print(f"  Plaintext:  0x{plaintext:032X}")
    print(f"  Key:        0x{master_key:048X}")
    print(f"  Ciphertext: 0x{ciphertext:032X}")
    print(f"  Decrypted:  0x{decrypted:032X}")

    ok = decrypted == plaintext
    print("  ✅ Round-trip PASSED" if ok else "  ❌ Round-trip FAILED")

    extra_ok = True
    for pt_extra, key_extra in [
        (0, 0),
        ((1 << 128) - 1, (1 << 192) - 1),
        (0x0102030405060708090A0B0C0D0E0F10, 0x0807060504030201 << 128 | 0x0102030405060708090A0B0C0D0E0F10),
    ]:
        ct = lea_128_192_encrypt(pt_extra, key_extra)
        dec = lea_128_192_decrypt(ct, key_extra)
        if dec != pt_extra:
            extra_ok = False

    print("  ✅ Extra round-trip checks PASSED" if extra_ok else "  ❌ Extra round-trip checks FAILED")
    print("=" * 60)

    return ok and extra_ok


if __name__ == "__main__":
    success = test_lea_128_192()
    if not success:
        raise SystemExit(1)
