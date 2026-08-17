"""
SPECK-64/128 Block Cipher
==========================================
Block size: 64 bits (32 x 2 words)
Key size: 128 bits (4 x 32-bit words)
Rounds: 27
Round function: ARX (Add-Rotate-XOR)

Generated automatically from speck_template.py
"""



WORD_SIZE = 32
MASK = (1 << WORD_SIZE) - 1  # 0xFFFFFFFF

speck_64_128_alpha = 8
speck_64_128_beta = 3
speck_64_128_rounds = 27



def speck_64_128_rol(x: int, n: int) -> int:
    """
    Rotate left a 32-bit word.
    Matches Isabelle's word_rotl.
    """
    n = n % WORD_SIZE
    return ((x << n) | (x >> (WORD_SIZE - n))) & MASK


def speck_64_128_ror(x: int, n: int) -> int:
    """
    Rotate right a 32-bit word.
    Matches Isabelle's word_rotr.
    """
    n = n % WORD_SIZE
    return ((x >> n) | (x << (WORD_SIZE - n))) & MASK


def speck_64_128_encrypt_round(k: int, xy: tuple[int, int]) -> tuple[int, int]:
    """
    Single encryption round.
    
    Matches Isabelle definition:
    definition speck_64_128_encrypt_round
    
    Round function:
        x = (ROTR(x, alpha) + y) XOR k
        y = ROTL(y, beta) XOR x
    """
    x, y = xy
    x = (speck_64_128_ror(x, speck_64_128_alpha) + y) & MASK
    x ^= k
    y = speck_64_128_rol(y, speck_64_128_beta) ^ x
    return x, y


def speck_64_128_decrypt_round_inverse(k: int, xy: tuple[int, int]) -> tuple[int, int]:
    """
    Single decryption round (inverse).
    
    Matches Isabelle definition:
    definition speck_64_128_decrypt_round_inverse
    
    Inverse round function:
        y = ROTR(x XOR y, beta)
        x = ROTL((x XOR k) - y, alpha)
    """
    x, y = xy
    y = speck_64_128_ror(x ^ y, speck_64_128_beta)
    x = speck_64_128_rol(((x ^ k) - y) & MASK, speck_64_128_alpha)
    return x, y



def speck_64_128_gen_key_schedule_rec(l_keys: list[int], k_keys: list[int], i: int) -> list[int]:
    """Recursive key-schedule step (mirrors the Isabelle recursive helper
    speck_64_128_gen_key_schedule_rec)."""
    if i >= speck_64_128_rounds - 1:
        return k_keys
    rc = i & MASK
    l_index = i % len(l_keys) if i >= len(l_keys) else i
    new_l, new_k = speck_64_128_encrypt_round(rc, (l_keys[l_index], k_keys[i]))
    return speck_64_128_gen_key_schedule_rec(l_keys + [new_l], k_keys + [new_k], i + 1)


def speck_64_128_generate_key_schedule(initial_key_words: list[int]) -> list[int]:
    """
    Generate round keys from initial key words.
    
    For Speck-64/128:
    - 4 initial key words (each 32-bit)
    - Produces 27 round keys
    
    Args:
        initial_key_words: List of 4 key words (little-endian order)
    
    Returns:
        List of 27 round keys (each 32-bit)
    """
    if len(initial_key_words) != 4:
        raise ValueError(f"Speck-64/128 requires 4 key words, got {len(initial_key_words)}")
    
    # Initialize K array: first round key is the first key word
    k_keys = [initial_key_words[0]]
    
    # Initialize L array: remaining key words
    l_keys = initial_key_words[1:4]
    return speck_64_128_gen_key_schedule_rec(l_keys, k_keys, 0)



def speck_64_128_block_to_words(block: int) -> tuple[int, int]:
    """
    Convert a 64-bit block to two 32-bit words.
    
    Convention: x = high 32 bits, y = low 32 bits
    """
    x = (block >> WORD_SIZE) & MASK
    y = block & MASK
    return x, y


def speck_64_128_words_to_block(x: int, y: int) -> int:
    """Convert two 32-bit words to a 64-bit block."""
    return ((x & MASK) << WORD_SIZE) | (y & MASK)


def speck_64_128_key_to_words(master_key: int) -> list[int]:
    """Convert a 128-bit master key to 4 32-bit words (little-endian)."""
    return [(master_key >> (WORD_SIZE * i)) & MASK for i in range(4)]


def speck_64_128_encrypt_block(x: int, y: int, round_keys: list[int]) -> tuple[int, int]:
    """Encrypt a block represented as two words (mirrors the Isabelle
    pattern-matching recursion in speck_64_128_encrypt_block)."""
    if not round_keys:
        return x, y
    x, y = speck_64_128_encrypt_round(round_keys[0], (x, y))
    return speck_64_128_encrypt_block(x, y, round_keys[1:])


def speck_64_128_decrypt_block(x: int, y: int, round_keys: list[int]) -> tuple[int, int]:
    """Decrypt a block represented as two words."""
    for k in reversed(round_keys):
        x, y = speck_64_128_decrypt_round_inverse(k, (x, y))
    return x, y


def speck_64_128_encrypt(plaintext: int, master_key: int) -> int:
    """Top-level encryption for Speck-64/128."""
    key_words = speck_64_128_key_to_words(master_key)
    round_keys = speck_64_128_generate_key_schedule(key_words)
    x, y = speck_64_128_block_to_words(plaintext)
    x, y = speck_64_128_encrypt_block(x, y, round_keys)
    return speck_64_128_words_to_block(x, y)


def speck_64_128_decrypt(ciphertext: int, master_key: int) -> int:
    """Top-level decryption for Speck-64/128."""
    key_words = speck_64_128_key_to_words(master_key)
    round_keys = speck_64_128_generate_key_schedule(key_words)
    x, y = speck_64_128_block_to_words(ciphertext)
    x, y = speck_64_128_decrypt_block(x, y, round_keys)
    return speck_64_128_words_to_block(x, y)


def test_speck_64_128():
    """Test Speck-64/128 against reference vectors."""
    print("=" * 60)
    print(f"Testing Speck-64/128")
    print("=" * 60)

    # Test vector from arxpy reference
    plaintext = 0x3B7265747475432D
    master_key = 0x030201000B0A0908131211101B1A1918
    expected = 0x8C6FA548454E028B
    
    print(f"  Plaintext:  0x{plaintext:016X}")
    print(f"  Master Key: 0x{master_key:032X}")
    
    ciphertext = speck_64_128_encrypt(plaintext, master_key)
    decrypted = speck_64_128_decrypt(ciphertext, master_key)
    
    print(f"  Ciphertext: 0x{ciphertext:016X}")
    print(f"  Expected:   0x{expected:016X}")
    print(f"  Decrypted:  0x{decrypted:016X}")
    
    if ciphertext == expected:
        print("  ✅ Test PASSED (matches reference)")
    else:
        print("  ⚠️ Test may have endianness differences (check implementation)")
    
    if decrypted == plaintext:
        print("  ✅ Round-trip PASSED")
    else:
        print("  ❌ Round-trip FAILED")
    
    return ciphertext == expected and decrypted == plaintext


if __name__ == "__main__":
    test_speck_64_128()
