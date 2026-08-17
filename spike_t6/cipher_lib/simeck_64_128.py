"""
SIMECK-64/128 block cipher (single-variant, tiered implementation).

T1: Constants
T2: Primitives (rotation, round function, encrypt/decrypt round, round-key constant)
T3: Key schedule
T4: Orchestration (encrypt/decrypt/test)

Reference: Yang, Zhu, Suder, Aagaard, Gong, "The Simeck Family of
Lightweight Block Ciphers", CHES 2015 (eprint.iacr.org/2015/612).
Algorithm ported from designer Bo Zhu's own reference implementation
(github.com/bozhu/Simeck).
"""


WORD_SIZE = 32
BLOCK_SIZE = 64
KEY_SIZE = 128
ROUNDS = 44
KEY_WORDS = 4

WORD_MASK = (1 << WORD_SIZE) - 1
CONSTANT = WORD_MASK - 3  # 2^WORD_SIZE - 4


def simeck_64_128_generate_sequence() -> tuple[int, ...]:
    """LFSR-style bit sequence used to vary the round constant each round (rounds >= 40 variant)."""
    states = [1] * 6
    for i in range(ROUNDS - 5):
        feedback = states[i + 1] ^ states[i]
        states.append(feedback)
    return tuple(states)


SEQUENCE = simeck_64_128_generate_sequence()


def simeck_64_128_rol(x: int, r: int) -> int:
    """Rotate a 32-bit word left by r bits."""
    r %= WORD_SIZE
    return ((x << r) & WORD_MASK) | (x >> (WORD_SIZE - r))


def simeck_64_128_f(x: int) -> int:
    """SIMECK round function f(x) = (x & ROL5(x)) ^ ROL1(x)."""
    return ((x & simeck_64_128_rol(x, 5)) ^ simeck_64_128_rol(x, 1)) & WORD_MASK


def simeck_64_128_round_key_constant(round_index: int) -> int:
    """Round constant for round_index: CONSTANT with its low bit XORed by the sequence."""
    return (CONSTANT ^ SEQUENCE[round_index]) & WORD_MASK


def simeck_64_128_encrypt_round(x: int, y: int, k: int) -> tuple[int, int]:
    """One SIMECK encryption round (Feistel): (x, y) -> (y ^ f(x) ^ k, x)."""
    new_x = (y ^ simeck_64_128_f(x) ^ k) & WORD_MASK
    new_y = x
    return new_x, new_y


def simeck_64_128_decrypt_round(x: int, y: int, k: int) -> tuple[int, int]:
    """Inverse SIMECK round: (x, y) -> (y, x ^ f(y) ^ k)."""
    new_x = y
    new_y = (x ^ simeck_64_128_f(y) ^ k) & WORD_MASK
    return new_x, new_y


def simeck_64_128_key_to_words(master_key: int) -> tuple[int, int, int, int]:
    """Split the 128-bit key into 4 32-bit words (little-endian word order)."""
    t0 = master_key & WORD_MASK
    t1 = (master_key >> WORD_SIZE) & WORD_MASK
    t2 = (master_key >> (2 * WORD_SIZE)) & WORD_MASK
    t3 = (master_key >> (3 * WORD_SIZE)) & WORD_MASK
    return t0, t1, t2, t3


def simeck_64_128_generate_round_keys_rec(states: list[int], round_index: int) -> list[int]:
    """
    Recursive key schedule: at each round, emit states[0] as the round key,
    then advance the 4-word state register by one SIMECK round (reusing
    the round function itself, keyed by the round constant).
    """
    if round_index >= ROUNDS:
        return []
    round_key = states[0]
    left, right = states[1], states[0]
    left, right = simeck_64_128_encrypt_round(left, right, simeck_64_128_round_key_constant(round_index))
    next_states = [states[1], states[2], states[3], left]
    return [round_key] + simeck_64_128_generate_round_keys_rec(next_states, round_index + 1)


def simeck_64_128_generate_round_keys(master_key: int) -> list[int]:
    """Generate all 44 round keys for SIMECK-64/128."""
    t0, t1, t2, t3 = simeck_64_128_key_to_words(master_key)
    return simeck_64_128_generate_round_keys_rec([t0, t1, t2, t3], 0)


def simeck_64_128_block_to_words(block: int) -> tuple[int, int]:
    """Split the 64-bit block into two 32-bit words (left=high, right=low)."""
    left = (block >> WORD_SIZE) & WORD_MASK
    right = block & WORD_MASK
    return left, right


def simeck_64_128_words_to_block(left: int, right: int) -> int:
    """Pack two 32-bit words into one 64-bit block."""
    return ((left & WORD_MASK) << WORD_SIZE) | (right & WORD_MASK)


def simeck_64_128_encrypt_rounds_iterate(x: int, y: int, round_keys: list[int], i: int) -> tuple[int, int]:
    """Recursive encryption iterator over all 44 rounds."""
    if i >= ROUNDS:
        return x, y
    x, y = simeck_64_128_encrypt_round(x, y, round_keys[i])
    return simeck_64_128_encrypt_rounds_iterate(x, y, round_keys, i + 1)


def simeck_64_128_decrypt_rounds_iterate(x: int, y: int, round_keys: list[int], i: int) -> tuple[int, int]:
    """Recursive decryption iterator: rounds consumed in reverse (43 down to 0)."""
    if i >= ROUNDS:
        return x, y
    round_index = ROUNDS - 1 - i
    x, y = simeck_64_128_decrypt_round(x, y, round_keys[round_index])
    return simeck_64_128_decrypt_rounds_iterate(x, y, round_keys, i + 1)


def simeck_64_128_encrypt_block(plaintext: int, round_keys: list[int]) -> int:
    """Encrypt one 64-bit block using the precomputed round keys."""
    x, y = simeck_64_128_block_to_words(plaintext)
    x, y = simeck_64_128_encrypt_rounds_iterate(x, y, round_keys, 0)
    return simeck_64_128_words_to_block(x, y)


def simeck_64_128_decrypt_block(ciphertext: int, round_keys: list[int]) -> int:
    """Decrypt one 64-bit block using the precomputed round keys."""
    x, y = simeck_64_128_block_to_words(ciphertext)
    x, y = simeck_64_128_decrypt_rounds_iterate(x, y, round_keys, 0)
    return simeck_64_128_words_to_block(x, y)


def simeck_64_128_encrypt(plaintext: int, master_key: int) -> int:
    """Encrypt one 64-bit block under one 128-bit master key."""
    round_keys = simeck_64_128_generate_round_keys(master_key)
    return simeck_64_128_encrypt_block(plaintext, round_keys)


def simeck_64_128_decrypt(ciphertext: int, master_key: int) -> int:
    """Decrypt one 64-bit block under one 128-bit master key."""
    round_keys = simeck_64_128_generate_round_keys(master_key)
    return simeck_64_128_decrypt_block(ciphertext, round_keys)


def simeck_64_128_test() -> bool:
    """Official SIMECK64/128 test vector (designer's reference implementation) plus round-trip checks."""
    print("=" * 60)
    print("Testing SIMECK-64/128")
    print("=" * 60)

    plaintext1 = 0x656B696C20646E75
    key1 = 0x1B1A1918131211100B0A090803020100
    expected_ct1 = 0x45CE69025F7AB7ED

    ct1 = simeck_64_128_encrypt(plaintext1, key1)
    dec1 = simeck_64_128_decrypt(ct1, key1)
    ok1 = ct1 == expected_ct1 and dec1 == plaintext1
    print(f"Test Vector 1 (official): pt=0x{plaintext1:016X} key=0x{key1:032X}")
    print(f"  ct=0x{ct1:016X} expected=0x{expected_ct1:016X} dec=0x{dec1:016X}")
    print("  ✅ PASSED" if ok1 else "  ❌ FAILED")

    print("\nTest Vector 2 (zero values):")
    pt2, mk2 = 0x0, 0x0
    ct2 = simeck_64_128_encrypt(pt2, mk2)
    dec2 = simeck_64_128_decrypt(ct2, mk2)
    expected_ct2 = 0x89EE79D7CCD489D8
    ok2 = dec2 == pt2 and ct2 == expected_ct2
    print(f"  pt=0x{pt2:016X} key=0x{mk2:032X} ct=0x{ct2:016X} expected=0x{expected_ct2:016X} dec=0x{dec2:016X}")
    print("  ✅ PASSED" if ok2 else "  ❌ FAILED")

    print("\nTest Vector 3 (all ones):")
    pt3 = (1 << BLOCK_SIZE) - 1
    mk3 = (1 << KEY_SIZE) - 1
    ct3 = simeck_64_128_encrypt(pt3, mk3)
    dec3 = simeck_64_128_decrypt(ct3, mk3)
    expected_ct3 = 0x1E1FA2A7F1388FBB
    ok3 = dec3 == pt3 and ct3 == expected_ct3
    print(f"  pt=0x{pt3:016X} key=0x{mk3:032X} ct=0x{ct3:016X} expected=0x{expected_ct3:016X} dec=0x{dec3:016X}")
    print("  ✅ PASSED" if ok3 else "  ❌ FAILED")

    all_ok = ok1 and ok2 and ok3
    print()
    print("✅ All SIMECK-64/128 tests passed!" if all_ok else "❌ SIMECK-64/128 TEST FAILURE")
    print("=" * 60)
    return all_ok


if __name__ == "__main__":
    success = simeck_64_128_test()
    if not success:
        raise SystemExit(1)
