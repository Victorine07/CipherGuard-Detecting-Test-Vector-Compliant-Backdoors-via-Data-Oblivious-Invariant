"""
CHAM-64/128 Block Cipher
==========================================
Block size: 64 bits (4 x 16-bit words)
Key size: 128 bits (8 x 16-bit words)
Rounds: 80
Round function: ARX (Add-Rotate-XOR)

Structured for T1/T2/T3/T4 extraction.
Reference behavior adapted from the provided ArxPy CHAM implementation.
"""

WORD_SIZE = 16
MASK = (1 << WORD_SIZE) - 1

cham_64_128_block_size = 64
cham_64_128_key_size = 128
cham_64_128_word_size = WORD_SIZE
cham_64_128_block_words = 4
cham_64_128_key_words = 8
cham_64_128_round_key_words = 16
cham_64_128_rounds = 80


def cham_64_128_rol(x: int, n: int) -> int:
    """Rotate left a 16-bit word."""
    n %= WORD_SIZE
    return ((x << n) | (x >> (WORD_SIZE - n))) & MASK


def cham_64_128_ror(x: int, n: int) -> int:
    """Rotate right a 16-bit word."""
    n %= WORD_SIZE
    return ((x >> n) | (x << (WORD_SIZE - n))) & MASK


def cham_64_128_keymix_low(k: int) -> int:
    """Compute the low CHAM round-key component."""
    return (k ^ cham_64_128_rol(k, 1) ^ cham_64_128_rol(k, 8)) & MASK


def cham_64_128_keymix_high(k: int) -> int:
    """Compute the high CHAM round-key component."""
    return (k ^ cham_64_128_rol(k, 1) ^ cham_64_128_rol(k, 11)) & MASK


def cham_64_128_encrypt_round_even(state: tuple[int, int, int, int], rk: int, i: int) -> tuple[int, int, int, int]:
    """Apply an even CHAM encryption round."""
    x0, x1, x2, x3 = state
    y3 = cham_64_128_rol(((x0 ^ i) + (cham_64_128_rol(x1, 1) ^ rk)) & MASK, 8)
    return x1, x2, x3, y3


def cham_64_128_encrypt_round_odd(state: tuple[int, int, int, int], rk: int, i: int) -> tuple[int, int, int, int]:
    """Apply an odd CHAM encryption round."""
    x0, x1, x2, x3 = state
    y3 = cham_64_128_rol(((x0 ^ i) + (cham_64_128_rol(x1, 8) ^ rk)) & MASK, 1)
    return x1, x2, x3, y3


def cham_64_128_decrypt_round_even(state: tuple[int, int, int, int], rk: int, i: int) -> tuple[int, int, int, int]:
    """Invert an even CHAM encryption round."""
    y0, y1, y2, y3 = state
    x1, x2, x3 = y0, y1, y2
    temp = cham_64_128_ror(y3, 8)
    x0 = ((temp - (cham_64_128_rol(x1, 1) ^ rk)) & MASK) ^ i
    return x0 & MASK, x1, x2, x3


def cham_64_128_decrypt_round_odd(state: tuple[int, int, int, int], rk: int, i: int) -> tuple[int, int, int, int]:
    """Invert an odd CHAM encryption round."""
    y0, y1, y2, y3 = state
    x1, x2, x3 = y0, y1, y2
    temp = cham_64_128_ror(y3, 1)
    x0 = ((temp - (cham_64_128_rol(x1, 8) ^ rk)) & MASK) ^ i
    return x0 & MASK, x1, x2, x3


def cham_64_128_key_to_words(master_key: int) -> list[int]:
    """Convert a 128-bit master key to 8 little-endian 16-bit words."""
    return [(master_key >> (WORD_SIZE * i)) & MASK for i in range(cham_64_128_key_words)]


def cham_64_128_fill_round_keys(key_words: list[int], i: int, round_keys: list[int]) -> list[int]:
    """Recursively fill round keys starting at key index i (mirrors the
    Isabelle recursive helper cham_64_128_fill_round_keys)."""
    if i >= cham_64_128_key_words:
        return round_keys
    round_keys = list(round_keys)
    round_keys[i] = cham_64_128_keymix_low(key_words[i])
    round_keys[(i + cham_64_128_key_words) ^ 1] = cham_64_128_keymix_high(key_words[i])
    return cham_64_128_fill_round_keys(key_words, i + 1, round_keys)


def cham_64_128_generate_round_keys(key_words: list[int]) -> list[int]:
    """Generate CHAM-64/128 round keys."""
    if len(key_words) != cham_64_128_key_words:
        raise ValueError(f"CHAM-64/128 requires {cham_64_128_key_words} key words, got {len(key_words)}")

    return cham_64_128_fill_round_keys(key_words, 0, [0] * cham_64_128_round_key_words)


def cham_64_128_block_to_words(block: int) -> tuple[int, int, int, int]:
    """Convert a 64-bit block to four 16-bit words in little-endian order."""
    return tuple((block >> (WORD_SIZE * i)) & MASK for i in range(cham_64_128_block_words))


def cham_64_128_words_to_block(x0: int, x1: int, x2: int, x3: int) -> int:
    """Convert four 16-bit words in little-endian order to a 64-bit block."""
    return (
        (x0 & MASK)
        | ((x1 & MASK) << WORD_SIZE)
        | ((x2 & MASK) << (2 * WORD_SIZE))
        | ((x3 & MASK) << (3 * WORD_SIZE))
    )


def cham_64_128_encrypt_block_iter(
    state: tuple[int, int, int, int], round_keys: list[int], i: int
) -> tuple[int, int, int, int]:
    """Recursive round iterator for encryption (mirrors the Isabelle
    recursive helper cham_64_128_encrypt_block_iter)."""
    if i >= cham_64_128_rounds:
        return state
    rk = round_keys[i % cham_64_128_round_key_words]
    if i % 2 == 0:
        state = cham_64_128_encrypt_round_even(state, rk, i)
    else:
        state = cham_64_128_encrypt_round_odd(state, rk, i)
    return cham_64_128_encrypt_block_iter(state, round_keys, i + 1)


def cham_64_128_encrypt_block(x0: int, x1: int, x2: int, x3: int, round_keys: list[int]) -> tuple[int, int, int, int]:
    """Encrypt a block represented as four words."""
    return cham_64_128_encrypt_block_iter((x0, x1, x2, x3), round_keys, 0)


def cham_64_128_decrypt_block_iter(
    state: tuple[int, int, int, int], round_keys: list[int], j: int
) -> tuple[int, int, int, int]:
    """Recursive round iterator for decryption (mirrors the Isabelle
    recursive helper cham_64_128_decrypt_block_iter; j counts up from 0
    while the actual round index i = rounds - 1 - j counts down)."""
    if j >= cham_64_128_rounds:
        return state
    i = cham_64_128_rounds - 1 - j
    rk = round_keys[i % cham_64_128_round_key_words]
    if i % 2 == 0:
        state = cham_64_128_decrypt_round_even(state, rk, i)
    else:
        state = cham_64_128_decrypt_round_odd(state, rk, i)
    return cham_64_128_decrypt_block_iter(state, round_keys, j + 1)


def cham_64_128_decrypt_block(x0: int, x1: int, x2: int, x3: int, round_keys: list[int]) -> tuple[int, int, int, int]:
    """Decrypt a block represented as four words."""
    return cham_64_128_decrypt_block_iter((x0, x1, x2, x3), round_keys, 0)


def cham_64_128_encrypt(plaintext: int, master_key: int) -> int:
    """Top-level encryption for CHAM-64/128."""
    key_words = cham_64_128_key_to_words(master_key)
    round_keys = cham_64_128_generate_round_keys(key_words)
    x0, x1, x2, x3 = cham_64_128_block_to_words(plaintext)
    y0, y1, y2, y3 = cham_64_128_encrypt_block(x0, x1, x2, x3, round_keys)
    return cham_64_128_words_to_block(y0, y1, y2, y3)


def cham_64_128_decrypt(ciphertext: int, master_key: int) -> int:
    """Top-level decryption for CHAM-64/128."""
    key_words = cham_64_128_key_to_words(master_key)
    round_keys = cham_64_128_generate_round_keys(key_words)
    x0, x1, x2, x3 = cham_64_128_block_to_words(ciphertext)
    p0, p1, p2, p3 = cham_64_128_decrypt_block(x0, x1, x2, x3, round_keys)
    return cham_64_128_words_to_block(p0, p1, p2, p3)


def test_cham_64_128() -> bool:
    """Test CHAM-64/128 against the provided reference vector and round-trip decryption."""
    print("=" * 60)
    print("Testing CHAM-64/128")
    print("=" * 60)

    plaintext_words = (0x1100, 0x3322, 0x5544, 0x7766)
    key_words = (0x0100, 0x0302, 0x0504, 0x0706, 0x0908, 0x0B0A, 0x0D0C, 0x0F0E)
    expected_words = (0x453C, 0x63BC, 0xDCFA, 0xBF4E)

    plaintext = cham_64_128_words_to_block(*plaintext_words)
    master_key = sum((w & MASK) << (WORD_SIZE * i) for i, w in enumerate(key_words))
    expected_ciphertext = cham_64_128_words_to_block(*expected_words)

    ciphertext = cham_64_128_encrypt(plaintext, master_key)
    decrypted = cham_64_128_decrypt(ciphertext, master_key)

    print(f"  Plaintext : 0x{plaintext:016X}")
    print(f"  Key       : 0x{master_key:032X}")
    print(f"  Expected  : 0x{expected_ciphertext:016X}")
    print(f"  Computed  : 0x{ciphertext:016X}")
    print(f"  Decrypted : 0x{decrypted:016X}")

    ok_encrypt = ciphertext == expected_ciphertext
    ok_decrypt = decrypted == plaintext

    if ok_encrypt:
        print("  ✅ CHAM-64/128 encryption test vector PASSED")
    else:
        print("  ❌ CHAM-64/128 encryption test vector FAILED")

    if ok_decrypt:
        print("  ✅ CHAM-64/128 decryption round-trip PASSED")
    else:
        print("  ❌ CHAM-64/128 decryption round-trip FAILED")

    return ok_encrypt and ok_decrypt


if __name__ == "__main__":
    test_cham_64_128()