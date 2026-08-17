"""
SIMON-48/96 block cipher (single-variant, tiered implementation).

T1: Constants
T2: Primitives (rotations, round function, single round)
T3: Key schedule
T4: Orchestration (encrypt/decrypt/test)

Reference: NSA Simon Speck Implementation Guide
"""





WORD_SIZE = 24
BLOCK_SIZE = 48
KEY_SIZE = 96
ROUNDS = 36
KEY_WORDS = 4

WORD_MASK = (1 << WORD_SIZE) - 1  # 0xFFFFFF
ROUND_CONSTANT = WORD_MASK ^ 0x3  # 0xFFFFFC

# Z-sequence for SIMON-48/96 from the NSA implementation guide
# Bits are read LSB first in the key schedule
Z_SEQUENCE = 0x16864FB8AD0C9F71






def simon_48_96_rol(x: int, r: int) -> int:
    """Rotate a 24-bit word left by r bits."""
    r %= WORD_SIZE
    return ((x << r) & WORD_MASK) | (x >> (WORD_SIZE - r))


def simon_48_96_ror(x: int, r: int) -> int:
    """Rotate a 24-bit word right by r bits."""
    r %= WORD_SIZE
    return (x >> r) | ((x << (WORD_SIZE - r)) & WORD_MASK)


def simon_48_96_f(x: int) -> int:
    """
    SIMON round function f(x) = (ROL1(x) & ROL8(x)) ^ ROL2(x).
    This is the non-linear Feistel function.
    """
    return ((simon_48_96_rol(x, 1) & simon_48_96_rol(x, 8)) ^
            simon_48_96_rol(x, 2)) & WORD_MASK


def simon_48_96_encrypt_round(x: int, y: int, k: int) -> tuple[int, int]:
    """
    One SIMON encryption round (Feistel).

    Encryption: (x, y) -> (y ^ f(x) ^ k, x)
    """
    new_x = (y ^ simon_48_96_f(x) ^ k) & WORD_MASK
    new_y = x
    return new_x, new_y


def simon_48_96_decrypt_round(x: int, y: int, k: int) -> tuple[int, int]:
    """
    One SIMON decryption round (inverse of encryption round).

    Given encryption: (x, y) -> (y ^ f(x) ^ k, x)
    Inverse: (x, y) -> (y, x ^ f(y) ^ k)
    """
    new_x = y
    new_y = (x ^ simon_48_96_f(y) ^ k) & WORD_MASK
    return new_x, new_y






def simon_48_96_key_to_words(master_key: int) -> tuple[int, int, int, int]:
    """
    Split 96-bit key into 4 24-bit words (little-endian word order):
      K[0] = least significant word
      ...
      K[3] = most significant word
    """
    k0 = master_key & WORD_MASK
    k1 = (master_key >> 24) & WORD_MASK
    k2 = (master_key >> 48) & WORD_MASK
    k3 = (master_key >> 72) & WORD_MASK
    return k0, k1, k2, k3


def simon_48_96_generate_round_keys_rec(rk: list[int], z: int, i: int) -> list[int]:
    """Recursive round-key generator (mirrors the Isabelle recursive
    helper simon_48_96_generate_round_keys_rec)."""
    if i >= ROUNDS:
        return rk
    tmp = (
        rk[i - 4]
        ^ simon_48_96_ror(rk[i - 1], 3)
        ^ rk[i - 3]
        ^ simon_48_96_ror(rk[i - 1], 4)
        ^ simon_48_96_ror(rk[i - 3], 1)
    )
    new_k = (ROUND_CONSTANT ^ (z & 1) ^ tmp) & WORD_MASK
    # Cyclic rotate-right-by-1 within the 62-bit Z sequence period
    # (the official z0..z4 sequences are defined with period 62; a plain
    # linear shift would incorrectly read zeros once rounds exceed 62).
    z_next = ((z >> 1) | ((z & 1) << 61)) & ((1 << 62) - 1)
    return simon_48_96_generate_round_keys_rec(rk + [new_k], z_next, i + 1)


def simon_48_96_generate_round_keys(master_key: int) -> list[int]:
    """
    Generate 36 round keys for SIMON-48/96.
    """

    k0, k1, k2, k3 = simon_48_96_key_to_words(master_key)
    rk = [k0, k1, k2, k3]
    return simon_48_96_generate_round_keys_rec(rk, Z_SEQUENCE, 4)





def simon_48_96_block_to_words(block: int) -> tuple[int, int]:
    """
    Split 48-bit block into two 24-bit words (left, right):
      left  = high word
      right = low word

    Block packing: block = (left << WORD_SIZE) | right
    """
    left = (block >> WORD_SIZE) & WORD_MASK
    right = block & WORD_MASK
    return left, right


def simon_48_96_words_to_block(left: int, right: int) -> int:
    """
    Pack two 24-bit words (left, right) into one 48-bit block.
    """
    return ((left & WORD_MASK) << WORD_SIZE) | (right & WORD_MASK)


def simon_48_96_encrypt_block_iter(state: tuple[int, int], round_keys: list[int]) -> tuple[int, int]:
    """Recursively apply encrypt_round over the round-key list (mirrors
    the Isabelle pattern-matching recursion in simon_48_96_encrypt_block_iter)."""
    if not round_keys:
        return state
    x, y = state
    x, y = simon_48_96_encrypt_round(x, y, round_keys[0])
    return simon_48_96_encrypt_block_iter((x, y), round_keys[1:])


def simon_48_96_encrypt_block(plaintext: int, round_keys: list[int]) -> int:
    """
    Encrypt one 64-bit block using round keys.

    Iterates single-round Feistel encryption for all rounds.
    """
    state = simon_48_96_block_to_words(plaintext)
    x, y = simon_48_96_encrypt_block_iter(state, round_keys)
    return simon_48_96_words_to_block(x, y)


def simon_48_96_decrypt_block(ciphertext: int, round_keys: list[int]) -> int:
    """
    Decrypt one 48-bit block using round keys (reverse order).

    Iterates single-round Feistel decryption for all rounds in reverse.
    """
    x, y = simon_48_96_block_to_words(ciphertext)

    for k in reversed(round_keys):
        x, y = simon_48_96_decrypt_round(x, y, k)

    return simon_48_96_words_to_block(x, y)


def simon_48_96_encrypt(plaintext: int, master_key: int) -> int:
    """Encrypt one 48-bit plaintext block under one 96-bit master key."""
    round_keys = simon_48_96_generate_round_keys(master_key)
    return simon_48_96_encrypt_block(plaintext, round_keys)


def simon_48_96_decrypt(ciphertext: int, master_key: int) -> int:
    """Decrypt one 48-bit ciphertext block under one 96-bit master key."""
    round_keys = simon_48_96_generate_round_keys(master_key)
    return simon_48_96_decrypt_block(ciphertext, round_keys)





def simon_48_96_test() -> None:
    """
    Tests for SIMON-48/96:
    - official NSA vector where embedded
    - zero roundtrip
    - all-ones roundtrip
    """
    print("=" * 60)
    print("Testing SIMON-48/96")
    print("=" * 60)

    # Test Vector 1 (official)
    plaintext = simon_48_96_words_to_block(0x726963, 0x20646E)
    master_key = (
        (0x1A1918 << 72)
        | (0x121110 << 48)
        | (0xA0908 << 24)
        | 0x20100
    )
    expected_ciphertext = simon_48_96_words_to_block(0x6E06A5, 0xACF156)

    ciphertext = simon_48_96_encrypt(plaintext, master_key)
    decrypted = simon_48_96_decrypt(ciphertext, master_key)

    print(f"\nTest Vector 1:")
    print(f"  Plaintext:  0x{plaintext:012X}")
    print(f"  Key:        0x{master_key:024X}")
    print(f"  Ciphertext: 0x{ciphertext:012X}")
    print(f"  Expected:   0x{expected_ciphertext:012X}")
    print(f"  Decrypted:  0x{decrypted:012X}")

    assert ciphertext == expected_ciphertext, "Encryption FAILED"
    assert decrypted == plaintext, "Decryption FAILED"
    print("  ✅ PASSED")

    # Test Vector 2: zero values
    print("\nTest Vector 2 (zero values):")
    pt2 = 0x0
    mk2 = 0x0
    ct2 = simon_48_96_encrypt(pt2, mk2)
    dec2 = simon_48_96_decrypt(ct2, mk2)
    print(f"  Plaintext:  0x{pt2:012X}")
    print(f"  Ciphertext: 0x{ct2:012X}")
    print(f"  Decrypted:  0x{dec2:012X}")
    assert dec2 == pt2, "Zero-value roundtrip FAILED"
    print("  ✅ PASSED")

    # Test Vector 3: all ones
    print("\nTest Vector 3 (all ones):")
    pt3 = (1 << BLOCK_SIZE) - 1
    mk3 = (1 << KEY_SIZE) - 1
    ct3 = simon_48_96_encrypt(pt3, mk3)
    dec3 = simon_48_96_decrypt(ct3, mk3)
    print(f"  Plaintext:  0x{pt3:012X}")
    print(f"  Ciphertext: 0x{ct3:012X}")
    print(f"  Decrypted:  0x{dec3:012X}")
    assert dec3 == pt3, "All-ones roundtrip FAILED"
    print("  ✅ PASSED")

    print("\n" + "=" * 60)
    print("✅ All SIMON-48/96 tests passed!")
    print("=" * 60)


if __name__ == "__main__":
    simon_48_96_test()
