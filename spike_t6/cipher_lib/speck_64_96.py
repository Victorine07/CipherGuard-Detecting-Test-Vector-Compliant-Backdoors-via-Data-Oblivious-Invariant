"""
SPECK-64/96 Block Cipher
==========================================
Block size: 64 bits (32 x 2 words)
Key size: 96 bits (3 x 32-bit words)
Rounds: 26
Round function: ARX (Add-Rotate-XOR)

Generated automatically from speck_template.py
"""



WORD_SIZE = 32
MASK = (1 << WORD_SIZE) - 1  # 0xFFFFFFFF

speck_64_96_alpha = 8
speck_64_96_beta = 3
speck_64_96_rounds = 26



def speck_64_96_rol(x: int, n: int) -> int:
    """
    Rotate left a 32-bit word.
    Matches Isabelle's word_rotl.
    """
    n = n % WORD_SIZE
    return ((x << n) | (x >> (WORD_SIZE - n))) & MASK


def speck_64_96_ror(x: int, n: int) -> int:
    """
    Rotate right a 32-bit word.
    Matches Isabelle's word_rotr.
    """
    n = n % WORD_SIZE
    return ((x >> n) | (x << (WORD_SIZE - n))) & MASK


def speck_64_96_encrypt_round(k: int, xy: tuple[int, int]) -> tuple[int, int]:
    """
    Single encryption round.
    
    Matches Isabelle definition:
    definition speck_64_96_encrypt_round
    
    Round function:
        x = (ROTR(x, alpha) + y) XOR k
        y = ROTL(y, beta) XOR x
    """
    x, y = xy
    x = (speck_64_96_ror(x, speck_64_96_alpha) + y) & MASK
    x ^= k
    y = speck_64_96_rol(y, speck_64_96_beta) ^ x
    return x, y


def speck_64_96_decrypt_round_inverse(k: int, xy: tuple[int, int]) -> tuple[int, int]:
    """
    Single decryption round (inverse).
    
    Matches Isabelle definition:
    definition speck_64_96_decrypt_round_inverse
    
    Inverse round function:
        y = ROTR(x XOR y, beta)
        x = ROTL((x XOR k) - y, alpha)
    """
    x, y = xy
    y = speck_64_96_ror(x ^ y, speck_64_96_beta)
    x = speck_64_96_rol(((x ^ k) - y) & MASK, speck_64_96_alpha)
    return x, y



def speck_64_96_gen_key_schedule_rec(l_keys: list[int], k_keys: list[int], i: int) -> list[int]:
    """Recursive key-schedule step (mirrors the Isabelle recursive helper
    speck_64_96_gen_key_schedule_rec)."""
    if i >= speck_64_96_rounds - 1:
        return k_keys
    rc = i & MASK
    l_index = i % len(l_keys) if i >= len(l_keys) else i
    new_l, new_k = speck_64_96_encrypt_round(rc, (l_keys[l_index], k_keys[i]))
    return speck_64_96_gen_key_schedule_rec(l_keys + [new_l], k_keys + [new_k], i + 1)


def speck_64_96_generate_key_schedule(initial_key_words: list[int]) -> list[int]:
    """
    Generate round keys from initial key words.
    
    For Speck-64/96:
    - 3 initial key words (each 32-bit)
    - Produces 26 round keys
    
    Args:
        initial_key_words: List of 3 key words (little-endian order)
    
    Returns:
        List of 26 round keys (each 32-bit)
    """
    if len(initial_key_words) != 3:
        raise ValueError(f"Speck-64/96 requires 3 key words, got {len(initial_key_words)}")
    
    # Initialize K array: first round key is the first key word
    k_keys = [initial_key_words[0]]
    
    # Initialize L array: remaining key words
    l_keys = initial_key_words[1:3]
    return speck_64_96_gen_key_schedule_rec(l_keys, k_keys, 0)



def speck_64_96_block_to_words(block: int) -> tuple[int, int]:
    """
    Convert a 64-bit block to two 32-bit words.
    
    Convention: x = high 32 bits, y = low 32 bits
    """
    x = (block >> WORD_SIZE) & MASK
    y = block & MASK
    return x, y


def speck_64_96_words_to_block(x: int, y: int) -> int:
    """Convert two 32-bit words to a 64-bit block."""
    return ((x & MASK) << WORD_SIZE) | (y & MASK)


def speck_64_96_key_to_words(master_key: int) -> list[int]:
    """Convert a 96-bit master key to 3 32-bit words (little-endian)."""
    return [(master_key >> (WORD_SIZE * i)) & MASK for i in range(3)]


def speck_64_96_encrypt_block(x: int, y: int, round_keys: list[int]) -> tuple[int, int]:
    """Encrypt a block represented as two words (mirrors the Isabelle
    pattern-matching recursion in speck_64_96_encrypt_block)."""
    if not round_keys:
        return x, y
    x, y = speck_64_96_encrypt_round(round_keys[0], (x, y))
    return speck_64_96_encrypt_block(x, y, round_keys[1:])


def speck_64_96_decrypt_block(x: int, y: int, round_keys: list[int]) -> tuple[int, int]:
    """Decrypt a block represented as two words."""
    for k in reversed(round_keys):
        x, y = speck_64_96_decrypt_round_inverse(k, (x, y))
    return x, y


def speck_64_96_encrypt(plaintext: int, master_key: int) -> int:
    """Top-level encryption for Speck-64/96."""
    key_words = speck_64_96_key_to_words(master_key)
    round_keys = speck_64_96_generate_key_schedule(key_words)
    x, y = speck_64_96_block_to_words(plaintext)
    x, y = speck_64_96_encrypt_block(x, y, round_keys)
    return speck_64_96_words_to_block(x, y)


def speck_64_96_decrypt(ciphertext: int, master_key: int) -> int:
    """Top-level decryption for Speck-64/96."""
    key_words = speck_64_96_key_to_words(master_key)
    round_keys = speck_64_96_generate_key_schedule(key_words)
    x, y = speck_64_96_block_to_words(ciphertext)
    x, y = speck_64_96_decrypt_block(x, y, round_keys)
    return speck_64_96_words_to_block(x, y)



def test_speck_64_96():
    """Test Speck-64/96 against reference vectors."""
    print("=" * 60)
    print(f"Testing Speck-64/96")
    print("=" * 60)

    # Test vector from arxpy reference
    plaintext = 0x74614620736E6165
    master_key = 0x030201000B0A090813121110
    expected = 0x9F7952EC4175946C
    
    print(f"  Plaintext:  0x{plaintext:016X}")
    print(f"  Master Key: 0x{master_key:024X}")
    
    ciphertext = speck_64_96_encrypt(plaintext, master_key)
    decrypted = speck_64_96_decrypt(ciphertext, master_key)
    
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
    test_speck_64_96()
