"""
SPARX-64/128 Block Cipher
=========================
Reference implementation matching the official CryptoLUX reference
implementation (Dinu, Perrin, Udovenko, Velichkov, Grossschadl,
Biryukov, "Design Strategies for ARX-based Symmetric-Key Ciphers",
CHES 2016; https://github.com/cryptolu/SPARX, ref-c/sparx.c) and the
Isabelle/HOL formalization in thy ciphers/Sparx_64_128.thy.

T1: Constants
T2: Primitives (rotations, A-permutation, linear layer, single round)
T3: Structural Components (key schedule)
T4: Orchestration (step/branch/round iteration, encrypt/decrypt)

Variant: SPARX-64/128 -- 64-bit block (4 x 16-bit words, 2 branches),
128-bit key (8 x 16-bit words), 8 steps, 3 rounds/step.
"""


SPARX_64_128_BLOCK_SIZE = 64
SPARX_64_128_KEY_SIZE = 128
SPARX_64_128_N_STEPS = 8
SPARX_64_128_ROUNDS_PER_STEP = 3
SPARX_64_128_WORD_SIZE = 16
SPARX_64_128_N_BRANCHES = 2
SPARX_64_128_N_WORDS = 4
SPARX_64_128_ROUND_KEY_WORDS = 2
SPARX_64_128_MASK = 0xFFFF


def sparx_64_128_rol(x: int, n: int) -> int:
    return ((x << n) | (x >> (SPARX_64_128_WORD_SIZE - n))) & SPARX_64_128_MASK


def sparx_64_128_ror(x: int, n: int) -> int:
    return ((x >> n) | (x << (SPARX_64_128_WORD_SIZE - n))) & SPARX_64_128_MASK


def sparx_64_128_a_perm(l: int, r: int) -> tuple[int, int]:
    """The keyless ARX-box ('A' permutation) shared by the round
    function and the key schedule."""
    l = sparx_64_128_rol(l, 9)
    l = (l + r) & SPARX_64_128_MASK
    r = sparx_64_128_rol(r, 2)
    r ^= l
    return l, r


def sparx_64_128_a_perm_inv(l: int, r: int) -> tuple[int, int]:
    r ^= l
    r = sparx_64_128_rol(r, 14)
    l = (l - r) & SPARX_64_128_MASK
    l = sparx_64_128_rol(l, 7)
    return l, r


def sparx_64_128_l_w(x: int) -> int:
    return sparx_64_128_rol(x, 8)


def sparx_64_128_linear_layer(state: list[int]) -> list[int]:
    x0, x1, x2, x3 = state
    t = sparx_64_128_l_w(x0 ^ x1)
    return [x2 ^ x0 ^ t, x3 ^ x1 ^ t, x0, x1]


def sparx_64_128_linear_layer_inv(state: list[int]) -> list[int]:
    y0, y1, y2, y3 = state
    x0, x1 = y2, y3
    t = sparx_64_128_l_w(x0 ^ x1)
    return [x0, x1, y0 ^ x0 ^ t, y1 ^ x1 ^ t]


def sparx_64_128_apply_encrypt_round(x0: int, x1: int, key1: int, key2: int) -> tuple[int, int]:
    """One encryption round on a single branch's pair of words."""
    x0 ^= key1
    x1 ^= key2
    return sparx_64_128_a_perm(x0, x1)


def sparx_64_128_apply_decrypt_round(x0: int, x1: int, key1: int, key2: int) -> tuple[int, int]:
    """One decryption round on a single branch's pair of words."""
    x0, x1 = sparx_64_128_a_perm_inv(x0, x1)
    x0 ^= key1
    x1 ^= key2
    return x0, x1


def sparx_64_128_extract_key_words(master_key: int) -> list[int]:
    return [(master_key >> (16 * i)) & SPARX_64_128_MASK for i in range(8)]


def sparx_64_128_k_perm(k: list[int], c: int) -> list[int]:
    """The key-state permutation (Misty-like transformation + branch
    rotation), mirroring K_perm_64_128 in the official reference."""
    k = k[:]
    k[0], k[1] = sparx_64_128_a_perm(k[0], k[1])
    k[2] = (k[2] + k[0]) & SPARX_64_128_MASK
    k[3] = (k[3] + k[1]) & SPARX_64_128_MASK
    k[7] = (k[7] + c) & SPARX_64_128_MASK
    new_k = [0] * 8
    new_k[0], new_k[1] = k[6], k[7]
    new_k[2], new_k[3], new_k[4], new_k[5], new_k[6], new_k[7] = k[0], k[1], k[2], k[3], k[4], k[5]
    return new_k


def sparx_64_128_gen_key_schedule_iterate(
    k: list[int], c: int, max_c: int, acc: list[list[int]]
) -> list[list[int]]:
    """Recursive key-schedule accumulator: each step captures a row of
    2*ROUNDS_PER_STEP words from the current key state, then advances
    the state by one k_perm call (mirrors the Isabelle recursive
    helper sparx_64_128_gen_key_schedule_iterate)."""
    if c >= max_c:
        return acc
    row = k[0:2 * SPARX_64_128_ROUNDS_PER_STEP]
    return sparx_64_128_gen_key_schedule_iterate(
        sparx_64_128_k_perm(k, c + 1), c + 1, max_c, acc + [row]
    )


def sparx_64_128_generate_key_schedule(master_key: int) -> list[list[int]]:
    k = sparx_64_128_extract_key_words(master_key)
    max_c = SPARX_64_128_N_BRANCHES * SPARX_64_128_N_STEPS + 1
    return sparx_64_128_gen_key_schedule_iterate(k, 0, max_c, [])


def sparx_64_128_block_to_words(block: int) -> list[int]:
    return [(block >> (16 * i)) & SPARX_64_128_MASK for i in range(SPARX_64_128_N_WORDS)]


def sparx_64_128_words_to_block(words: list[int]) -> int:
    acc = 0
    for i in range(SPARX_64_128_N_WORDS):
        acc |= (words[i] & SPARX_64_128_MASK) << (16 * i)
    return acc


def sparx_64_128_encrypt_round_iterate(
    x0: int, x1: int, all_keys: list[list[int]], row: int, r: int
) -> tuple[int, int]:
    """Recursively apply ROUNDS_PER_STEP encryption rounds to one
    branch (mirrors the Isabelle recursive helper
    sparx_64_128_encrypt_round_iterate)."""
    if r >= SPARX_64_128_ROUNDS_PER_STEP:
        return x0, x1
    key1 = all_keys[row][2 * r]
    key2 = all_keys[row][2 * r + 1]
    x0, x1 = sparx_64_128_apply_encrypt_round(x0, x1, key1, key2)
    return sparx_64_128_encrypt_round_iterate(x0, x1, all_keys, row, r + 1)


def sparx_64_128_decrypt_round_iterate(
    x0: int, x1: int, all_keys: list[list[int]], row: int, r: int
) -> tuple[int, int]:
    """Recursively apply ROUNDS_PER_STEP decryption rounds (in reverse)
    to one branch (mirrors the Isabelle recursive helper
    sparx_64_128_decrypt_round_iterate)."""
    if r < 0:
        return x0, x1
    key1 = all_keys[row][2 * r]
    key2 = all_keys[row][2 * r + 1]
    x0, x1 = sparx_64_128_apply_decrypt_round(x0, x1, key1, key2)
    return sparx_64_128_decrypt_round_iterate(x0, x1, all_keys, row, r - 1)


def sparx_64_128_encrypt_step_iterate(state: list[int], all_keys: list[list[int]], step: int) -> list[int]:
    """One full step: every branch runs ROUNDS_PER_STEP encryption
    rounds (mirrors the Isabelle recursive helper
    sparx_64_128_encrypt_step_iterate)."""
    state = state[:]
    for b in range(SPARX_64_128_N_BRANCHES):
        row = SPARX_64_128_N_BRANCHES * step + b
        x0, x1 = sparx_64_128_encrypt_round_iterate(state[2 * b], state[2 * b + 1], all_keys, row, 0)
        state[2 * b], state[2 * b + 1] = x0, x1
    return state


def sparx_64_128_decrypt_step_iterate(state: list[int], all_keys: list[list[int]], step: int) -> list[int]:
    """One full step: every branch runs ROUNDS_PER_STEP decryption
    rounds in reverse (mirrors the Isabelle recursive helper
    sparx_64_128_decrypt_step_iterate)."""
    state = state[:]
    for b in range(SPARX_64_128_N_BRANCHES):
        row = SPARX_64_128_N_BRANCHES * step + b
        x0, x1 = sparx_64_128_decrypt_round_iterate(
            state[2 * b], state[2 * b + 1], all_keys, row, SPARX_64_128_ROUNDS_PER_STEP - 1
        )
        state[2 * b], state[2 * b + 1] = x0, x1
    return state


def sparx_64_128_encrypt_steps_iterate(state: list[int], all_keys: list[list[int]], step: int) -> list[int]:
    """Recursively iterate all N_STEPS encryption steps, applying the
    linear layer between steps (mirrors the Isabelle recursive helper
    sparx_64_128_encrypt_steps_iterate)."""
    if step >= SPARX_64_128_N_STEPS:
        return state
    state = sparx_64_128_encrypt_step_iterate(state, all_keys, step)
    state = sparx_64_128_linear_layer(state)
    return sparx_64_128_encrypt_steps_iterate(state, all_keys, step + 1)


def sparx_64_128_decrypt_steps_iterate(state: list[int], all_keys: list[list[int]], step: int) -> list[int]:
    """Recursively iterate all N_STEPS decryption steps in reverse,
    applying the inverse linear layer before each step (mirrors the
    Isabelle recursive helper sparx_64_128_decrypt_steps_iterate)."""
    if step < 0:
        return state
    state = sparx_64_128_linear_layer_inv(state)
    state = sparx_64_128_decrypt_step_iterate(state, all_keys, step)
    return sparx_64_128_decrypt_steps_iterate(state, all_keys, step - 1)


def sparx_64_128_encrypt_block(plaintext: int, all_keys: list[list[int]]) -> int:
    state = sparx_64_128_block_to_words(plaintext)
    state = sparx_64_128_encrypt_steps_iterate(state, all_keys, 0)
    whitening_row = SPARX_64_128_N_BRANCHES * SPARX_64_128_N_STEPS
    for b in range(SPARX_64_128_N_BRANCHES):
        state[2 * b] ^= all_keys[whitening_row][2 * b]
        state[2 * b + 1] ^= all_keys[whitening_row][2 * b + 1]
    return sparx_64_128_words_to_block(state)


def sparx_64_128_decrypt_block(ciphertext: int, all_keys: list[list[int]]) -> int:
    state = sparx_64_128_block_to_words(ciphertext)
    whitening_row = SPARX_64_128_N_BRANCHES * SPARX_64_128_N_STEPS
    for b in range(SPARX_64_128_N_BRANCHES):
        state[2 * b] ^= all_keys[whitening_row][2 * b]
        state[2 * b + 1] ^= all_keys[whitening_row][2 * b + 1]
    state = sparx_64_128_decrypt_steps_iterate(state, all_keys, SPARX_64_128_N_STEPS - 1)
    return sparx_64_128_words_to_block(state)


def sparx_64_128_encrypt(plaintext: int, master_key: int) -> int:
    all_keys = sparx_64_128_generate_key_schedule(master_key)
    return sparx_64_128_encrypt_block(plaintext, all_keys)


def sparx_64_128_decrypt(ciphertext: int, master_key: int) -> int:
    all_keys = sparx_64_128_generate_key_schedule(master_key)
    return sparx_64_128_decrypt_block(ciphertext, all_keys)


def test_sparx_64_128() -> bool:
    """Official test vector from the CryptoLUX reference implementation
    (https://github.com/cryptolu/SPARX, ref-c/sparx.c)."""
    print("=" * 60)
    print("Testing SPARX-64/128")
    print("=" * 60)

    key_words = [0x0011, 0x2233, 0x4455, 0x6677, 0x8899, 0xAABB, 0xCCDD, 0xEEFF]
    plaintext_words = [0x0123, 0x4567, 0x89AB, 0xCDEF]
    expected_ciphertext_words = [0x2BBE, 0xF152, 0x01F5, 0x5F98]

    master_key = sum((w & SPARX_64_128_MASK) << (16 * i) for i, w in enumerate(key_words))
    plaintext = sparx_64_128_words_to_block(plaintext_words)
    expected_ciphertext = sum((w & SPARX_64_128_MASK) << (16 * i) for i, w in enumerate(expected_ciphertext_words))

    ciphertext = sparx_64_128_encrypt(plaintext, master_key)
    decrypted = sparx_64_128_decrypt(ciphertext, master_key)

    print(f"  Key words:        {[hex(x) for x in key_words]}")
    print(f"  Plaintext words:  {[hex(x) for x in plaintext_words]}")
    print(f"  Ciphertext words: {[hex(x) for x in sparx_64_128_block_to_words(ciphertext)]}")
    print(f"  Expected:         {[hex(x) for x in expected_ciphertext_words]}")

    ok_enc = ciphertext == expected_ciphertext
    ok_dec = decrypted == plaintext
    print("  ✅ Ciphertext PASSED" if ok_enc else "  ❌ Ciphertext FAILED")
    print("  ✅ Round-trip PASSED" if ok_dec else "  ❌ Round-trip FAILED")
    print("=" * 60)

    return ok_enc and ok_dec


if __name__ == "__main__":
    success = test_sparx_64_128()
    if not success:
        raise SystemExit(1)
