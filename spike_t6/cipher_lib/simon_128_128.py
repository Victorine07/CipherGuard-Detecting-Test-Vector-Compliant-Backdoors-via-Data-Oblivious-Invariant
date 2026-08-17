"""
SIMON-128/128 block cipher (single-variant, tiered implementation).

T1: Constants
T2: Primitives (rotations, round function, single round)
T3: Key schedule
T4: Orchestration (encrypt/decrypt/test)

Reference: NSA Simon Speck Implementation Guide
"""





WORD_SIZE = 64
BLOCK_SIZE = 128
KEY_SIZE = 128
ROUNDS = 68
KEY_WORDS = 2

WORD_MASK = (1 << WORD_SIZE) - 1  # 0xFFFFFFFFFFFFFFFF
ROUND_CONSTANT = WORD_MASK ^ 0x3  # 0xFFFFFFFFFFFFFFFC

# Z-sequence for SIMON-128/128 from the NSA implementation guide
# Bits are read LSB first in the key schedule
Z_SEQUENCE = 0x3369F885192C0EF5






def simon_128_128_rol(x: int, r: int) -> int:
    """Rotate a 64-bit word left by r bits."""
    r %= WORD_SIZE
    return ((x << r) & WORD_MASK) | (x >> (WORD_SIZE - r))


def simon_128_128_ror(x: int, r: int) -> int:
    """Rotate a 64-bit word right by r bits."""
    r %= WORD_SIZE
    return (x >> r) | ((x << (WORD_SIZE - r)) & WORD_MASK)


def simon_128_128_f(x: int) -> int:
    """
    SIMON round function f(x) = (ROL1(x) & ROL8(x)) ^ ROL2(x).
    This is the non-linear Feistel function.
    """
    return ((simon_128_128_rol(x, 1) & simon_128_128_rol(x, 8)) ^
            simon_128_128_rol(x, 2)) & WORD_MASK


def simon_128_128_encrypt_round(x: int, y: int, k: int) -> tuple[int, int]:
    """
    One SIMON encryption round (Feistel).

    Encryption: (x, y) -> (y ^ f(x) ^ k, x)
    """
    new_x = (y ^ simon_128_128_f(x) ^ k) & WORD_MASK
    new_y = x
    return new_x, new_y


def simon_128_128_decrypt_round(x: int, y: int, k: int) -> tuple[int, int]:
    """
    One SIMON decryption round (inverse of encryption round).

    Given encryption: (x, y) -> (y ^ f(x) ^ k, x)
    Inverse: (x, y) -> (y, x ^ f(y) ^ k)
    """
    new_x = y
    new_y = (x ^ simon_128_128_f(y) ^ k) & WORD_MASK
    return new_x, new_y






def simon_128_128_key_to_words(master_key: int) -> tuple[int, int]:
    """
    Split 128-bit key into 2 64-bit words (little-endian word order):
      K[0] = least significant word
      ...
      K[1] = most significant word
    """
    k0 = master_key & WORD_MASK
    k1 = (master_key >> 64) & WORD_MASK
    return k0, k1


def simon_128_128_generate_round_keys_rec(rk: list[int], z: int, i: int) -> list[int]:
    """Recursive round-key generator (mirrors the Isabelle recursive
    helper simon_128_128_generate_round_keys_rec)."""
    if i >= ROUNDS:
        return rk
    tmp = (
        rk[i - 2]
        ^ simon_128_128_ror(rk[i - 1], 3)
        ^ simon_128_128_ror(rk[i - 1], 4)
    )
    new_k = (ROUND_CONSTANT ^ (z & 1) ^ tmp) & WORD_MASK
    # Cyclic rotate-right-by-1 within the 62-bit Z sequence period
    # (the official z0..z4 sequences are defined with period 62; a plain
    # linear shift would incorrectly read zeros once rounds exceed 62).
    z_next = ((z >> 1) | ((z & 1) << 61)) & ((1 << 62) - 1)
    return simon_128_128_generate_round_keys_rec(rk + [new_k], z_next, i + 1)


def simon_128_128_generate_round_keys(master_key: int) -> list[int]:
    """
    Generate 68 round keys for SIMON-128/128.
    """

    k0, k1 = simon_128_128_key_to_words(master_key)
    rk = [k0, k1]
    return simon_128_128_generate_round_keys_rec(rk, Z_SEQUENCE, 2)





def simon_128_128_block_to_words(block: int) -> tuple[int, int]:
    """
    Split 128-bit block into two 64-bit words (left, right):
      left  = high word
      right = low word

    Block packing: block = (left << WORD_SIZE) | right
    """
    left = (block >> WORD_SIZE) & WORD_MASK
    right = block & WORD_MASK
    return left, right


def simon_128_128_words_to_block(left: int, right: int) -> int:
    """
    Pack two 64-bit words (left, right) into one 128-bit block.
    """
    return ((left & WORD_MASK) << WORD_SIZE) | (right & WORD_MASK)


def simon_128_128_encrypt_block_iter(state: tuple[int, int], round_keys: list[int]) -> tuple[int, int]:
    """Recursively apply encrypt_round over the round-key list (mirrors
    the Isabelle pattern-matching recursion in simon_128_128_encrypt_block_iter)."""
    if not round_keys:
        return state
    x, y = state
    x, y = simon_128_128_encrypt_round(x, y, round_keys[0])
    return simon_128_128_encrypt_block_iter((x, y), round_keys[1:])


def simon_128_128_encrypt_block(plaintext: int, round_keys: list[int]) -> int:
    """
    Encrypt one 64-bit block using round keys.

    Iterates single-round Feistel encryption for all rounds.
    """
    state = simon_128_128_block_to_words(plaintext)
    x, y = simon_128_128_encrypt_block_iter(state, round_keys)
    return simon_128_128_words_to_block(x, y)


def simon_128_128_decrypt_block(ciphertext: int, round_keys: list[int]) -> int:
    """
    Decrypt one 128-bit block using round keys (reverse order).

    Iterates single-round Feistel decryption for all rounds in reverse.
    """
    x, y = simon_128_128_block_to_words(ciphertext)

    for k in reversed(round_keys):
        x, y = simon_128_128_decrypt_round(x, y, k)

    return simon_128_128_words_to_block(x, y)


def simon_128_128_encrypt(plaintext: int, master_key: int) -> int:
    """Encrypt one 128-bit plaintext block under one 128-bit master key."""
    round_keys = simon_128_128_generate_round_keys(master_key)
    return simon_128_128_encrypt_block(plaintext, round_keys)


def simon_128_128_decrypt(ciphertext: int, master_key: int) -> int:
    """Decrypt one 128-bit ciphertext block under one 128-bit master key."""
    round_keys = simon_128_128_generate_round_keys(master_key)
    return simon_128_128_decrypt_block(ciphertext, round_keys)





def simon_128_128_test() -> None:
    """
    Tests for SIMON-128/128:
    - official NSA vector where embedded
    - zero roundtrip
    - all-ones roundtrip
    """
    print("=" * 60)
    print("Testing SIMON-128/128")
    print("=" * 60)

    # Test Vector 1 (official)
    plaintext = simon_128_128_words_to_block(0x6373656420737265, 0x6C6C657661727420)
    master_key = (
        (0xF0E0D0C0B0A0908 << 64)
        | 0x706050403020100
    )
    expected_ciphertext = simon_128_128_words_to_block(0x49681B1E1E54FE3F, 0x65AA832AF84E0BBC)

    ciphertext = simon_128_128_encrypt(plaintext, master_key)
    decrypted = simon_128_128_decrypt(ciphertext, master_key)

    print(f"\nTest Vector 1:")
    print(f"  Plaintext:  0x{plaintext:032X}")
    print(f"  Key:        0x{master_key:032X}")
    print(f"  Ciphertext: 0x{ciphertext:032X}")
    print(f"  Expected:   0x{expected_ciphertext:032X}")
    print(f"  Decrypted:  0x{decrypted:032X}")

    assert ciphertext == expected_ciphertext, "Encryption FAILED"
    assert decrypted == plaintext, "Decryption FAILED"
    print("  ✅ PASSED")

    # Test Vector 2: zero values
    print("\nTest Vector 2 (zero values):")
    pt2 = 0x0
    mk2 = 0x0
    ct2 = simon_128_128_encrypt(pt2, mk2)
    dec2 = simon_128_128_decrypt(ct2, mk2)
    print(f"  Plaintext:  0x{pt2:032X}")
    print(f"  Ciphertext: 0x{ct2:032X}")
    print(f"  Decrypted:  0x{dec2:032X}")
    assert dec2 == pt2, "Zero-value roundtrip FAILED"
    print("  ✅ PASSED")

    # Test Vector 3: all ones
    print("\nTest Vector 3 (all ones):")
    pt3 = (1 << BLOCK_SIZE) - 1
    mk3 = (1 << KEY_SIZE) - 1
    ct3 = simon_128_128_encrypt(pt3, mk3)
    dec3 = simon_128_128_decrypt(ct3, mk3)
    print(f"  Plaintext:  0x{pt3:032X}")
    print(f"  Ciphertext: 0x{ct3:032X}")
    print(f"  Decrypted:  0x{dec3:032X}")
    assert dec3 == pt3, "All-ones roundtrip FAILED"
    print("  ✅ PASSED")

    print("\n" + "=" * 60)
    print("✅ All SIMON-128/128 tests passed!")
    print("=" * 60)


if __name__ == "__main__":
    simon_128_128_test()
