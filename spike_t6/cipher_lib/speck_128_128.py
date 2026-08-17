"""
SPECK-128/128 Block Cipher
==========================================
Block size: 128 bits (64 x 2 words)
Key size: 128 bits (2 x 64-bit words)
Rounds: 32
Round function: ARX (Add-Rotate-XOR)

Generated automatically from speck_template.py
"""



WORD_SIZE = 64
MASK = (1 << WORD_SIZE) - 1  # 0xFFFFFFFFFFFFFFFF

speck_128_128_alpha = 8
speck_128_128_beta = 3
speck_128_128_rounds = 32



def speck_128_128_rol(x: int, n: int) -> int:
    """
    Rotate left a 64-bit word.
    Matches Isabelle's word_rotl.
    """
    n = n % WORD_SIZE
    return ((x << n) | (x >> (WORD_SIZE - n))) & MASK


def speck_128_128_ror(x: int, n: int) -> int:
    """
    Rotate right a 64-bit word.
    Matches Isabelle's word_rotr.
    """
    n = n % WORD_SIZE
    return ((x >> n) | (x << (WORD_SIZE - n))) & MASK


def speck_128_128_encrypt_round(k: int, xy: tuple[int, int]) -> tuple[int, int]:
    """
    Single encryption round.
    
    Matches Isabelle definition:
    definition speck_128_128_encrypt_round
    
    Round function:
        x = (ROTR(x, alpha) + y) XOR k
        y = ROTL(y, beta) XOR x
    """
    x, y = xy
    x = (speck_128_128_ror(x, speck_128_128_alpha) + y) & MASK
    x ^= k
    y = speck_128_128_rol(y, speck_128_128_beta) ^ x
    return x, y


def speck_128_128_decrypt_round_inverse(k: int, xy: tuple[int, int]) -> tuple[int, int]:
    """
    Single decryption round (inverse).
    
    Matches Isabelle definition:
    definition speck_128_128_decrypt_round_inverse
    
    Inverse round function:
        y = ROTR(x XOR y, beta)
        x = ROTL((x XOR k) - y, alpha)
    """
    x, y = xy
    y = speck_128_128_ror(x ^ y, speck_128_128_beta)
    x = speck_128_128_rol(((x ^ k) - y) & MASK, speck_128_128_alpha)
    return x, y




def speck_128_128_gen_key_schedule_rec(l_keys: list[int], k_keys: list[int], i: int) -> list[int]:
    """Recursive key-schedule step (mirrors the Isabelle recursive helper
    speck_128_128_gen_key_schedule_rec)."""
    if i >= speck_128_128_rounds - 1:
        return k_keys
    rc = i & MASK
    l_index = i % len(l_keys) if i >= len(l_keys) else i
    new_l, new_k = speck_128_128_encrypt_round(rc, (l_keys[l_index], k_keys[i]))
    return speck_128_128_gen_key_schedule_rec(l_keys + [new_l], k_keys + [new_k], i + 1)


def speck_128_128_generate_key_schedule(initial_key_words: list[int]) -> list[int]:
    """
    Generate round keys from initial key words.
    
    For Speck-128/128:
    - 2 initial key words (each 64-bit)
    - Produces 32 round keys
    
    Args:
        initial_key_words: List of 2 key words (little-endian order)
    
    Returns:
        List of 32 round keys (each 64-bit)
    """
    if len(initial_key_words) != 2:
        raise ValueError(f"Speck-128/128 requires 2 key words, got {len(initial_key_words)}")
    
    # Initialize K array: first round key is the first key word
    k_keys = [initial_key_words[0]]
    
    # Initialize L array: remaining key words
    l_keys = initial_key_words[1:2]
    return speck_128_128_gen_key_schedule_rec(l_keys, k_keys, 0)




def speck_128_128_block_to_words(block: int) -> tuple[int, int]:
    """
    Convert a 128-bit block to two 64-bit words.
    
    Convention: x = high 64 bits, y = low 64 bits
    """
    x = (block >> WORD_SIZE) & MASK
    y = block & MASK
    return x, y


def speck_128_128_words_to_block(x: int, y: int) -> int:
    """Convert two 64-bit words to a 128-bit block."""
    return ((x & MASK) << WORD_SIZE) | (y & MASK)


def speck_128_128_key_to_words(master_key: int) -> list[int]:
    """Convert a 128-bit master key to 2 64-bit words (little-endian)."""
    return [(master_key >> (WORD_SIZE * i)) & MASK for i in range(2)]


def speck_128_128_encrypt_block(x: int, y: int, round_keys: list[int]) -> tuple[int, int]:
    """Encrypt a block represented as two words (mirrors the Isabelle
    pattern-matching recursion in speck_128_128_encrypt_block)."""
    if not round_keys:
        return x, y
    x, y = speck_128_128_encrypt_round(round_keys[0], (x, y))
    return speck_128_128_encrypt_block(x, y, round_keys[1:])


def speck_128_128_decrypt_block(x: int, y: int, round_keys: list[int]) -> tuple[int, int]:
    """Decrypt a block represented as two words."""
    for k in reversed(round_keys):
        x, y = speck_128_128_decrypt_round_inverse(k, (x, y))
    return x, y


def speck_128_128_encrypt(plaintext: int, master_key: int) -> int:
    """Top-level encryption for Speck-128/128."""
    key_words = speck_128_128_key_to_words(master_key)
    round_keys = speck_128_128_generate_key_schedule(key_words)
    x, y = speck_128_128_block_to_words(plaintext)
    x, y = speck_128_128_encrypt_block(x, y, round_keys)
    return speck_128_128_words_to_block(x, y)


def speck_128_128_decrypt(ciphertext: int, master_key: int) -> int:
    """Top-level decryption for Speck-128/128."""
    key_words = speck_128_128_key_to_words(master_key)
    round_keys = speck_128_128_generate_key_schedule(key_words)
    x, y = speck_128_128_block_to_words(ciphertext)
    x, y = speck_128_128_decrypt_block(x, y, round_keys)
    return speck_128_128_words_to_block(x, y)





def test_speck_128_128():
    """Test Speck-128/128 against reference vectors."""
    print("=" * 60)
    print(f"Testing Speck-128/128")
    print("=" * 60)

    print(f"  No test vector available for Speck-128/128")
    print("  Testing round-trip only...")
    
    # Simple round-trip test
    plaintext = 0x12345678 & ((1 << 128) - 1)
    master_key = 0x0123456789ABCDEF & ((1 << 128) - 1)
    
    ciphertext = speck_128_128_encrypt(plaintext, master_key)
    decrypted = speck_128_128_decrypt(ciphertext, master_key)
    
    block_hex_width = 128 // 4
    key_hex_width = 128 // 4
    
    print(f"  Plaintext:  0x{plaintext:0{block_hex_width}X}")
    print(f"  Ciphertext: 0x{ciphertext:0{block_hex_width}X}")
    print(f"  Decrypted:  0x{decrypted:0{block_hex_width}X}")
    
    if decrypted == plaintext:
        print("  ✅ Round-trip PASSED")
    else:
        print("  ❌ Round-trip FAILED")
    
    return decrypted == plaintext


if __name__ == "__main__":
    test_speck_128_128()
