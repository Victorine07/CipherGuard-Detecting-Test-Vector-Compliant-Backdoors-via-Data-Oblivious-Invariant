"""
SIMECK-48/96 block cipher (single-variant, tiered implementation).

T1: Constants
T2: Primitives (rotation, round function, encrypt/decrypt round, round-key constant)
T3: Key schedule
T4: Orchestration (encrypt/decrypt/test)

Reference: Yang, Zhu, Suder, Aagaard, Gong, "The Simeck Family of
Lightweight Block Ciphers", CHES 2015 (eprint.iacr.org/2015/612).
Algorithm ported from designer Bo Zhu's own reference implementation
(github.com/bozhu/Simeck).
"""


WORD_SIZE = 24
BLOCK_SIZE = 48
KEY_SIZE = 96
ROUNDS = 36
KEY_WORDS = 4

WORD_MASK = (1 << WORD_SIZE) - 1
CONSTANT = WORD_MASK - 3  # 2^WORD_SIZE - 4


def simeck_48_96_generate_sequence() -> tuple[int, ...]:
    """LFSR-style bit sequence used to vary the round constant each round."""
    states = [1] * 5
    for i in range(ROUNDS - 5):
        feedback = states[i + 2] ^ states[i]
        states.append(feedback)
    return tuple(states)


SEQUENCE = simeck_48_96_generate_sequence()


def simeck_48_96_rol(x: int, r: int) -> int:
    """Rotate a 24-bit word left by r bits."""
    r %= WORD_SIZE
    return ((x << r) & WORD_MASK) | (x >> (WORD_SIZE - r))


def simeck_48_96_f(x: int) -> int:
    """SIMECK round function f(x) = (x & ROL5(x)) ^ ROL1(x)."""
    return ((x & simeck_48_96_rol(x, 5)) ^ simeck_48_96_rol(x, 1)) & WORD_MASK


def simeck_48_96_round_key_constant(round_index: int) -> int:
    """Round constant for round_index: CONSTANT with its low bit XORed by the sequence."""
    return (CONSTANT ^ SEQUENCE[round_index]) & WORD_MASK


def simeck_48_96_encrypt_round(x: int, y: int, k: int) -> tuple[int, int]:
    """One SIMECK encryption round (Feistel): (x, y) -> (y ^ f(x) ^ k, x)."""
    new_x = (y ^ simeck_48_96_f(x) ^ k) & WORD_MASK
    new_y = x
    return new_x, new_y


def simeck_48_96_decrypt_round(x: int, y: int, k: int) -> tuple[int, int]:
    """Inverse SIMECK round: (x, y) -> (y, x ^ f(y) ^ k)."""
    new_x = y
    new_y = (x ^ simeck_48_96_f(y) ^ k) & WORD_MASK
    return new_x, new_y


def simeck_48_96_key_to_words(master_key: int) -> tuple[int, int, int, int]:
    """Split the 96-bit key into 4 24-bit words (little-endian word order)."""
    t0 = master_key & WORD_MASK
    t1 = (master_key >> WORD_SIZE) & WORD_MASK
    t2 = (master_key >> (2 * WORD_SIZE)) & WORD_MASK
    t3 = (master_key >> (3 * WORD_SIZE)) & WORD_MASK
    return t0, t1, t2, t3


def simeck_48_96_generate_round_keys_rec(states: list[int], round_index: int) -> list[int]:
    """
    Recursive key schedule: at each round, emit states[0] as the round key,
    then advance the 4-word state register by one SIMECK round (reusing
    the round function itself, keyed by the round constant).
    """
    if round_index >= ROUNDS:
        return []
    round_key = states[0]
    left, right = states[1], states[0]
    left, right = simeck_48_96_encrypt_round(left, right, simeck_48_96_round_key_constant(round_index))
    next_states = [states[1], states[2], states[3], left]
    return [round_key] + simeck_48_96_generate_round_keys_rec(next_states, round_index + 1)


def simeck_48_96_generate_round_keys(master_key: int) -> list[int]:
    """Generate all 36 round keys for SIMECK-48/96."""
    t0, t1, t2, t3 = simeck_48_96_key_to_words(master_key)
    return simeck_48_96_generate_round_keys_rec([t0, t1, t2, t3], 0)


def simeck_48_96_block_to_words(block: int) -> tuple[int, int]:
    """Split the 48-bit block into two 24-bit words (left=high, right=low)."""
    left = (block >> WORD_SIZE) & WORD_MASK
    right = block & WORD_MASK
    return left, right


def simeck_48_96_words_to_block(left: int, right: int) -> int:
    """Pack two 24-bit words into one 48-bit block."""
    return ((left & WORD_MASK) << WORD_SIZE) | (right & WORD_MASK)


def simeck_48_96_encrypt_rounds_iterate(x: int, y: int, round_keys: list[int], i: int) -> tuple[int, int]:
    """Recursive encryption iterator over all 36 rounds."""
    if i >= ROUNDS:
        return x, y
    x, y = simeck_48_96_encrypt_round(x, y, round_keys[i])
    return simeck_48_96_encrypt_rounds_iterate(x, y, round_keys, i + 1)


def simeck_48_96_decrypt_rounds_iterate(x: int, y: int, round_keys: list[int], i: int) -> tuple[int, int]:
    """Recursive decryption iterator: rounds consumed in reverse (35 down to 0)."""
    if i >= ROUNDS:
        return x, y
    round_index = ROUNDS - 1 - i
    x, y = simeck_48_96_decrypt_round(x, y, round_keys[round_index])
    return simeck_48_96_decrypt_rounds_iterate(x, y, round_keys, i + 1)


def simeck_48_96_encrypt_block(plaintext: int, round_keys: list[int]) -> int:
    """Encrypt one 48-bit block using the precomputed round keys."""
    x, y = simeck_48_96_block_to_words(plaintext)
    x, y = simeck_48_96_encrypt_rounds_iterate(x, y, round_keys, 0)
    return simeck_48_96_words_to_block(x, y)


def simeck_48_96_decrypt_block(ciphertext: int, round_keys: list[int]) -> int:
    """Decrypt one 48-bit block using the precomputed round keys."""
    x, y = simeck_48_96_block_to_words(ciphertext)
    x, y = simeck_48_96_decrypt_rounds_iterate(x, y, round_keys, 0)
    return simeck_48_96_words_to_block(x, y)


def simeck_48_96_encrypt(plaintext: int, master_key: int) -> int:
    """Encrypt one 48-bit block under one 96-bit master key."""
    round_keys = simeck_48_96_generate_round_keys(master_key)
    return simeck_48_96_encrypt_block(plaintext, round_keys)


def simeck_48_96_decrypt(ciphertext: int, master_key: int) -> int:
    """Decrypt one 48-bit block under one 96-bit master key."""
    round_keys = simeck_48_96_generate_round_keys(master_key)
    return simeck_48_96_decrypt_block(ciphertext, round_keys)


def simeck_48_96_test() -> bool:
    """Official SIMECK48/96 test vector (designer's reference implementation) plus round-trip checks."""
    print("=" * 60)
    print("Testing SIMECK-48/96")
    print("=" * 60)

    plaintext1 = 0x72696320646E
    key1 = 0x1A19181211100A0908020100
    expected_ct1 = 0xF3CF25E33B36

    ct1 = simeck_48_96_encrypt(plaintext1, key1)
    dec1 = simeck_48_96_decrypt(ct1, key1)
    ok1 = ct1 == expected_ct1 and dec1 == plaintext1
    print(f"Test Vector 1 (official): pt=0x{plaintext1:012X} key=0x{key1:024X}")
    print(f"  ct=0x{ct1:012X} expected=0x{expected_ct1:012X} dec=0x{dec1:012X}")
    print("  ✅ PASSED" if ok1 else "  ❌ FAILED")

    print("\nTest Vector 2 (zero values):")
    pt2, mk2 = 0x0, 0x0
    ct2 = simeck_48_96_encrypt(pt2, mk2)
    dec2 = simeck_48_96_decrypt(ct2, mk2)
    ok2 = dec2 == pt2
    print(f"  pt=0x{pt2:012X} key=0x{mk2:024X} ct=0x{ct2:012X} dec=0x{dec2:012X}")
    print("  ✅ PASSED" if ok2 else "  ❌ FAILED")

    print("\nTest Vector 3 (all ones):")
    pt3 = (1 << BLOCK_SIZE) - 1
    mk3 = (1 << KEY_SIZE) - 1
    ct3 = simeck_48_96_encrypt(pt3, mk3)
    dec3 = simeck_48_96_decrypt(ct3, mk3)
    ok3 = dec3 == pt3
    expected_ct3 = 0xB036AD9E621E
    ok3 = ok3 and ct3 == expected_ct3
    print(f"  pt=0x{pt3:012X} key=0x{mk3:024X} ct=0x{ct3:012X} expected=0x{expected_ct3:012X} dec=0x{dec3:012X}")
    print("  ✅ PASSED" if ok3 else "  ❌ FAILED")

    all_ok = ok1 and ok2 and ok3
    print()
    print("✅ All SIMECK-48/96 tests passed!" if all_ok else "❌ SIMECK-48/96 TEST FAILURE")
    print("=" * 60)
    return all_ok


if __name__ == "__main__":
    success = simeck_48_96_test()
    if not success:
        raise SystemExit(1)
