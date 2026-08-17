"""
SPARX-128/128 Block Cipher
==========================
Reference implementation matching the official CryptoLUX reference
implementation (Dinu, Perrin, Udovenko, Velichkov, Grossschadl,
Biryukov, "Design Strategies for ARX-based Symmetric-Key Ciphers",
CHES 2016; https://github.com/cryptolu/SPARX, ref-c/sparx.c) and the
Isabelle/HOL formalization in thy ciphers/Sparx_128_128.thy.

T1: Constants
T2: Primitives (rotations, A-permutation, linear layer, single round)
T3: Structural Components (key schedule)
T4: Orchestration (step/branch/round iteration, encrypt/decrypt)

Variant: SPARX-128/128 -- 128-bit block (8 x 16-bit words, 4 branches),
128-bit key (8 x 16-bit words), 8 steps, 4 rounds/step.
"""


SPARX_128_128_BLOCK_SIZE = 128
SPARX_128_128_KEY_SIZE = 128
SPARX_128_128_N_STEPS = 8
SPARX_128_128_ROUNDS_PER_STEP = 4
SPARX_128_128_WORD_SIZE = 16
SPARX_128_128_N_BRANCHES = 4
SPARX_128_128_N_WORDS = 8
SPARX_128_128_ROUND_KEY_WORDS = 2
SPARX_128_128_MASK = 0xFFFF


def sparx_128_128_rol(x: int, n: int) -> int:
    return ((x << n) | (x >> (SPARX_128_128_WORD_SIZE - n))) & SPARX_128_128_MASK


def sparx_128_128_ror(x: int, n: int) -> int:
    return ((x >> n) | (x << (SPARX_128_128_WORD_SIZE - n))) & SPARX_128_128_MASK


def sparx_128_128_a_perm(l: int, r: int) -> tuple[int, int]:
    l = sparx_128_128_rol(l, 9)
    l = (l + r) & SPARX_128_128_MASK
    r = sparx_128_128_rol(r, 2)
    r ^= l
    return l, r


def sparx_128_128_a_perm_inv(l: int, r: int) -> tuple[int, int]:
    r ^= l
    r = sparx_128_128_rol(r, 14)
    l = (l - r) & SPARX_128_128_MASK
    l = sparx_128_128_rol(l, 7)
    return l, r


def sparx_128_128_l_w(x: int) -> int:
    return sparx_128_128_rol(x, 8)


def sparx_128_128_linear_layer(state: list[int]) -> list[int]:
    x0, x1, x2, x3, x4, x5, x6, x7 = state
    t = sparx_128_128_l_w(x0 ^ x1 ^ x2 ^ x3)
    return [
        x4 ^ x2 ^ t, x5 ^ x1 ^ t, x6 ^ x0 ^ t, x7 ^ x3 ^ t,
        x0, x1, x2, x3,
    ]


def sparx_128_128_linear_layer_inv(state: list[int]) -> list[int]:
    y0, y1, y2, y3, y4, y5, y6, y7 = state
    x0, x1, x2, x3 = y4, y5, y6, y7
    t = sparx_128_128_l_w(x0 ^ x1 ^ x2 ^ x3)
    return [
        x0, x1, x2, x3,
        y0 ^ x2 ^ t, y1 ^ x1 ^ t, y2 ^ x0 ^ t, y3 ^ x3 ^ t,
    ]


def sparx_128_128_apply_encrypt_round(x0: int, x1: int, key1: int, key2: int) -> tuple[int, int]:
    x0 ^= key1
    x1 ^= key2
    return sparx_128_128_a_perm(x0, x1)


def sparx_128_128_apply_decrypt_round(x0: int, x1: int, key1: int, key2: int) -> tuple[int, int]:
    x0, x1 = sparx_128_128_a_perm_inv(x0, x1)
    x0 ^= key1
    x1 ^= key2
    return x0, x1


def sparx_128_128_extract_key_words(master_key: int) -> list[int]:
    return [(master_key >> (16 * i)) & SPARX_128_128_MASK for i in range(8)]


def sparx_128_128_k_perm(k: list[int], c: int) -> list[int]:
    """Mirrors K_perm_128_128 in the official reference: two A-perm
    applications (on k0,k1 and on k4,k5), then the same branch
    rotation as the 64/128 variant."""
    k = k[:]
    k[0], k[1] = sparx_128_128_a_perm(k[0], k[1])
    k[2] = (k[2] + k[0]) & SPARX_128_128_MASK
    k[3] = (k[3] + k[1]) & SPARX_128_128_MASK
    k[4], k[5] = sparx_128_128_a_perm(k[4], k[5])
    k[6] = (k[6] + k[4]) & SPARX_128_128_MASK
    k[7] = (k[7] + k[5] + c) & SPARX_128_128_MASK
    new_k = [0] * 8
    new_k[0], new_k[1] = k[6], k[7]
    new_k[2], new_k[3], new_k[4], new_k[5], new_k[6], new_k[7] = k[0], k[1], k[2], k[3], k[4], k[5]
    return new_k


def sparx_128_128_gen_key_schedule_iterate(
    k: list[int], c: int, max_c: int, acc: list[list[int]]
) -> list[list[int]]:
    """Recursive key-schedule accumulator (mirrors the Isabelle
    recursive helper sparx_128_128_gen_key_schedule_iterate)."""
    if c >= max_c:
        return acc
    row = k[0:2 * SPARX_128_128_ROUNDS_PER_STEP]
    return sparx_128_128_gen_key_schedule_iterate(
        sparx_128_128_k_perm(k, c + 1), c + 1, max_c, acc + [row]
    )


def sparx_128_128_generate_key_schedule(master_key: int) -> list[list[int]]:
    k = sparx_128_128_extract_key_words(master_key)
    max_c = SPARX_128_128_N_BRANCHES * SPARX_128_128_N_STEPS + 1
    return sparx_128_128_gen_key_schedule_iterate(k, 0, max_c, [])


def sparx_128_128_block_to_words(block: int) -> list[int]:
    return [(block >> (16 * i)) & SPARX_128_128_MASK for i in range(SPARX_128_128_N_WORDS)]


def sparx_128_128_words_to_block(words: list[int]) -> int:
    acc = 0
    for i in range(SPARX_128_128_N_WORDS):
        acc |= (words[i] & SPARX_128_128_MASK) << (16 * i)
    return acc


def sparx_128_128_encrypt_round_iterate(
    x0: int, x1: int, all_keys: list[list[int]], row: int, r: int
) -> tuple[int, int]:
    """Recursively apply ROUNDS_PER_STEP encryption rounds to one
    branch (mirrors the Isabelle recursive helper
    sparx_128_128_encrypt_round_iterate)."""
    if r >= SPARX_128_128_ROUNDS_PER_STEP:
        return x0, x1
    key1 = all_keys[row][2 * r]
    key2 = all_keys[row][2 * r + 1]
    x0, x1 = sparx_128_128_apply_encrypt_round(x0, x1, key1, key2)
    return sparx_128_128_encrypt_round_iterate(x0, x1, all_keys, row, r + 1)


def sparx_128_128_decrypt_round_iterate(
    x0: int, x1: int, all_keys: list[list[int]], row: int, r: int
) -> tuple[int, int]:
    """Recursively apply ROUNDS_PER_STEP decryption rounds (in reverse)
    to one branch (mirrors the Isabelle recursive helper
    sparx_128_128_decrypt_round_iterate)."""
    if r < 0:
        return x0, x1
    key1 = all_keys[row][2 * r]
    key2 = all_keys[row][2 * r + 1]
    x0, x1 = sparx_128_128_apply_decrypt_round(x0, x1, key1, key2)
    return sparx_128_128_decrypt_round_iterate(x0, x1, all_keys, row, r - 1)


def sparx_128_128_encrypt_step_iterate(state: list[int], all_keys: list[list[int]], step: int) -> list[int]:
    """One full step: every branch runs ROUNDS_PER_STEP encryption
    rounds (mirrors the Isabelle recursive helper
    sparx_128_128_encrypt_step_iterate)."""
    state = state[:]
    for b in range(SPARX_128_128_N_BRANCHES):
        row = SPARX_128_128_N_BRANCHES * step + b
        x0, x1 = sparx_128_128_encrypt_round_iterate(state[2 * b], state[2 * b + 1], all_keys, row, 0)
        state[2 * b], state[2 * b + 1] = x0, x1
    return state


def sparx_128_128_decrypt_step_iterate(state: list[int], all_keys: list[list[int]], step: int) -> list[int]:
    """One full step: every branch runs ROUNDS_PER_STEP decryption
    rounds in reverse (mirrors the Isabelle recursive helper
    sparx_128_128_decrypt_step_iterate)."""
    state = state[:]
    for b in range(SPARX_128_128_N_BRANCHES):
        row = SPARX_128_128_N_BRANCHES * step + b
        x0, x1 = sparx_128_128_decrypt_round_iterate(
            state[2 * b], state[2 * b + 1], all_keys, row, SPARX_128_128_ROUNDS_PER_STEP - 1
        )
        state[2 * b], state[2 * b + 1] = x0, x1
    return state


def sparx_128_128_encrypt_steps_iterate(state: list[int], all_keys: list[list[int]], step: int) -> list[int]:
    """Recursively iterate all N_STEPS encryption steps, applying the
    linear layer between steps (mirrors the Isabelle recursive helper
    sparx_128_128_encrypt_steps_iterate)."""
    if step >= SPARX_128_128_N_STEPS:
        return state
    state = sparx_128_128_encrypt_step_iterate(state, all_keys, step)
    state = sparx_128_128_linear_layer(state)
    return sparx_128_128_encrypt_steps_iterate(state, all_keys, step + 1)


def sparx_128_128_decrypt_steps_iterate(state: list[int], all_keys: list[list[int]], step: int) -> list[int]:
    """Recursively iterate all N_STEPS decryption steps in reverse,
    applying the inverse linear layer before each step (mirrors the
    Isabelle recursive helper sparx_128_128_decrypt_steps_iterate)."""
    if step < 0:
        return state
    state = sparx_128_128_linear_layer_inv(state)
    state = sparx_128_128_decrypt_step_iterate(state, all_keys, step)
    return sparx_128_128_decrypt_steps_iterate(state, all_keys, step - 1)


def sparx_128_128_encrypt_block(plaintext: int, all_keys: list[list[int]]) -> int:
    state = sparx_128_128_block_to_words(plaintext)
    state = sparx_128_128_encrypt_steps_iterate(state, all_keys, 0)
    whitening_row = SPARX_128_128_N_BRANCHES * SPARX_128_128_N_STEPS
    for b in range(SPARX_128_128_N_BRANCHES):
        state[2 * b] ^= all_keys[whitening_row][2 * b]
        state[2 * b + 1] ^= all_keys[whitening_row][2 * b + 1]
    return sparx_128_128_words_to_block(state)


def sparx_128_128_decrypt_block(ciphertext: int, all_keys: list[list[int]]) -> int:
    state = sparx_128_128_block_to_words(ciphertext)
    whitening_row = SPARX_128_128_N_BRANCHES * SPARX_128_128_N_STEPS
    for b in range(SPARX_128_128_N_BRANCHES):
        state[2 * b] ^= all_keys[whitening_row][2 * b]
        state[2 * b + 1] ^= all_keys[whitening_row][2 * b + 1]
    state = sparx_128_128_decrypt_steps_iterate(state, all_keys, SPARX_128_128_N_STEPS - 1)
    return sparx_128_128_words_to_block(state)


def sparx_128_128_encrypt(plaintext: int, master_key: int) -> int:
    all_keys = sparx_128_128_generate_key_schedule(master_key)
    return sparx_128_128_encrypt_block(plaintext, all_keys)


def sparx_128_128_decrypt(ciphertext: int, master_key: int) -> int:
    all_keys = sparx_128_128_generate_key_schedule(master_key)
    return sparx_128_128_decrypt_block(ciphertext, all_keys)


def test_sparx_128_128() -> bool:
    """Official test vector from the CryptoLUX reference implementation
    (https://github.com/cryptolu/SPARX, ref-c/sparx.c)."""
    print("=" * 60)
    print("Testing SPARX-128/128")
    print("=" * 60)

    key_words = [0x0011, 0x2233, 0x4455, 0x6677, 0x8899, 0xAABB, 0xCCDD, 0xEEFF]
    plaintext_words = [0x0123, 0x4567, 0x89AB, 0xCDEF, 0xFEDC, 0xBA98, 0x7654, 0x3210]
    expected_ciphertext_words = [0x1CEE, 0x7540, 0x7DBF, 0x23D8, 0xE0EE, 0x1597, 0xF428, 0x52D8]

    master_key = sum((w & SPARX_128_128_MASK) << (16 * i) for i, w in enumerate(key_words))
    plaintext = sparx_128_128_words_to_block(plaintext_words)
    expected_ciphertext = sum((w & SPARX_128_128_MASK) << (16 * i) for i, w in enumerate(expected_ciphertext_words))

    ciphertext = sparx_128_128_encrypt(plaintext, master_key)
    decrypted = sparx_128_128_decrypt(ciphertext, master_key)

    print(f"  Key words:        {[hex(x) for x in key_words]}")
    print(f"  Plaintext words:  {[hex(x) for x in plaintext_words]}")
    print(f"  Ciphertext words: {[hex(x) for x in sparx_128_128_block_to_words(ciphertext)]}")
    print(f"  Expected:         {[hex(x) for x in expected_ciphertext_words]}")

    ok_enc = ciphertext == expected_ciphertext
    ok_dec = decrypted == plaintext
    print("  ✅ Ciphertext PASSED" if ok_enc else "  ❌ Ciphertext FAILED")
    print("  ✅ Round-trip PASSED" if ok_dec else "  ❌ Round-trip FAILED")
    print("=" * 60)

    return ok_enc and ok_dec


if __name__ == "__main__":
    success = test_sparx_128_128()
    if not success:
        raise SystemExit(1)
