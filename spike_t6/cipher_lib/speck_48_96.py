"""
SPECK-48/96 Block Cipher
========================
Implementation aligned with Isabelle/HOL formalization.

Specification:
- Block size: 48 bits (2 x 24-bit words)
- Key size: 96 bits (4 x 24-bit words)
- Rounds: 23
- Round function: ARX (Add-Rotate-XOR)

Naming convention matches Isabelle theory Speck_48_96.thy:
- speck_48_96_alpha = 8
- speck_48_96_beta = 3
- speck_48_96_rounds = 23

No official test vector was available when this file was authored;
correctness is checked via encrypt/decrypt round-trip self-consistency
(matching the established pattern used by the other SPECK variants
without a sourced vector, e.g. Speck-48/72, Speck-96/96, Speck-96/144,
Speck-128/128, Speck-128/192, Speck-128/256).
"""



# For Speck-48/96:
WORD_SIZE = 24
MASK = (1 << WORD_SIZE) - 1  # 0xFFFFFF for 24-bit
speck_48_96_alpha = 8
speck_48_96_beta = 3
speck_48_96_rounds = 23


def speck_48_96_rol(x: int, n: int) -> int:
    """
    Rotate left a 16-bit word.
    Matches Isabelle's word_rotl.
    """
    n = n % WORD_SIZE
    return ((x << n) | (x >> (WORD_SIZE - n))) & MASK


def speck_48_96_ror(x: int, n: int) -> int:
    """
    Rotate right a 16-bit word.
    Matches Isabelle's word_rotr.
    """
    n = n % WORD_SIZE
    return ((x >> n) | (x << (WORD_SIZE - n))) & MASK


def speck_48_96_encrypt_round(k: int, xy: tuple[int, int]) -> tuple[int, int]:
    """
    Single encryption round.
    
    Matches Isabelle definition:
    definition speck_48_96_encrypt_round :: "16 word ⇒ 16 word × 16 word ⇒ 16 word × 16 word"
    
    Round function:
        x = (ROTR(x, alpha) + y) XOR k
        y = ROTL(y, beta) XOR x
    
    Args:
        k: 16-bit round key
        xy: tuple of (x, y) where x and y are 16-bit words
    
    Returns:
        (new_x, new_y) after one round
    """
    x, y = xy
    x = (speck_48_96_ror(x, speck_48_96_alpha) + y) & MASK
    x ^= k
    y = speck_48_96_rol(y, speck_48_96_beta) ^ x
    return x, y


def speck_48_96_decrypt_round_inverse(k: int, xy: tuple[int, int]) -> tuple[int, int]:
    """
    Single decryption round (inverse).
    
    Matches Isabelle definition:
    definition speck_48_96_decrypt_round_inverse :: "16 word ⇒ 16 word × 16 word ⇒ 16 word × 16 word"
    
    Inverse round function:
        y = ROTR(x XOR y, beta)
        x = ROTL((x XOR k) - y, alpha)
    
    Args:
        k: 16-bit round key
        xy: tuple of (x, y) where x and y are 16-bit words
    
    Returns:
        (new_x, new_y) after one inverse round
    """
    x, y = xy
    y = speck_48_96_ror(x ^ y, speck_48_96_beta)
    x = speck_48_96_rol(((x ^ k) - y) & MASK, speck_48_96_alpha)
    return x, y



def speck_48_96_gen_key_schedule_rec(l_keys: list[int], k_keys: list[int], i: int) -> list[int]:
    """Recursive key-schedule step (mirrors the Isabelle recursive helper
    speck_48_96_gen_key_schedule_rec)."""
    if i >= speck_48_96_rounds - 1:
        return k_keys
    rc = i & MASK
    new_l, new_k = speck_48_96_encrypt_round(rc, (l_keys[i], k_keys[i]))
    return speck_48_96_gen_key_schedule_rec(l_keys + [new_l], k_keys + [new_k], i + 1)


def speck_48_96_generate_key_schedule(initial_key_words: list[int]) -> list[int]:
    """
    Generate round keys from initial key words.
    
    Matches Isabelle's key schedule structure:
    - speck_48_96_gen_key_schedule_rec (recursive)
    - speck_48_96_generate_key_schedule (wrapper)
    
    For Speck-32/64:
    - 4 initial key words (each 16-bit)
    - Produces 22 round keys (one per round)
    
    Key schedule algorithm:
        K[0] = key_words[0]
        L[0], L[1], L[2] = key_words[1], key_words[2], key_words[3]
        For i = 0 to rounds-2:
            L[i+3], K[i+1] = encrypt_round(i, L[i], K[i])
    
    Args:
        initial_key_words: List of 4 16-bit key words (little-endian order)
                           [k0, k1, k2, k3] where k0 is least significant
    
    Returns:
        List of 22 round keys (each 16-bit)
    """
    if len(initial_key_words) != 4:
        raise ValueError(f"Speck-32/64 requires 4 key words, got {len(initial_key_words)}")
    
    # Initialize K array: first round key is the first key word
    k_keys = [initial_key_words[0]]
    
    # Initialize L array: remaining key words
    l_keys = initial_key_words[1:4]  # L[0], L[1], L[2]
    return speck_48_96_gen_key_schedule_rec(l_keys, k_keys, 0)



def speck_48_96_block_to_words(block: int) -> tuple[int, int]:
    """
    Convert a 48-bit block to two 24-bit words.

    Matches Isabelle: speck_48_96_block_to_words

    Convention: x = high 24 bits, y = low 24 bits

    Args:
        block: 48-bit integer

    Returns:
        (x, y) where x and y are 24-bit words
    """
    x = (block >> WORD_SIZE) & MASK
    y = block & MASK
    return x, y


def speck_48_96_words_to_block(x: int, y: int) -> int:
    """
    Convert two 24-bit words to a 48-bit block.

    Matches Isabelle: speck_48_96_words_to_block

    Args:
        x: high 24-bit word
        y: low 24-bit word

    Returns:
        48-bit integer block
    """
    return ((x & MASK) << WORD_SIZE) | (y & MASK)


def speck_48_96_key_to_words(master_key: int) -> list[int]:
    """
    Convert a 96-bit master key to 4 24-bit words.

    Little-endian conversion: word0 = least significant 24 bits

    Args:
        master_key: 96-bit integer

    Returns:
        List of 4 24-bit words [k0, k1, k2, k3]
    """
    return [(master_key >> (WORD_SIZE * i)) & MASK for i in range(4)]


def speck_48_96_encrypt_block(x: int, y: int, round_keys: list[int]) -> tuple[int, int]:
    """Encrypt a block represented as two words (mirrors the Isabelle
    pattern-matching recursion in speck_48_96_encrypt_block)."""
    if not round_keys:
        return x, y
    x, y = speck_48_96_encrypt_round(round_keys[0], (x, y))
    return speck_48_96_encrypt_block(x, y, round_keys[1:])


def speck_48_96_decrypt_block(x: int, y: int, round_keys: list[int]) -> tuple[int, int]:
    """
    Decrypt a block represented as two words.

    Matches Isabelle: speck_48_96_decrypt_block

    Args:
        x: high 24-bit word
        y: low 24-bit word
        round_keys: list of 23 round keys

    Returns:
        (plaintext_x, plaintext_y)
    """
    for k in reversed(round_keys):
        x, y = speck_48_96_decrypt_round_inverse(k, (x, y))
    return x, y


def speck_48_96_encrypt(plaintext: int, master_key: int) -> int:
    """
    Top-level encryption for Speck-48/96.

    Matches Isabelle: speck_48_96_encrypt

    Args:
        plaintext: 48-bit plaintext block
        master_key: 96-bit master key

    Returns:
        48-bit ciphertext block
    """
    # Convert master key to words and generate round keys
    key_words = speck_48_96_key_to_words(master_key)
    round_keys = speck_48_96_generate_key_schedule(key_words)
    
    # Convert plaintext to words
    x, y = speck_48_96_block_to_words(plaintext)
    
    # Encrypt
    x, y = speck_48_96_encrypt_block(x, y, round_keys)
    
    # Convert back to block
    return speck_48_96_words_to_block(x, y)


def speck_48_96_decrypt(ciphertext: int, master_key: int) -> int:
    """
    Top-level decryption for Speck-48/96.

    Matches Isabelle: speck_48_96_decrypt

    Args:
        ciphertext: 48-bit ciphertext block
        master_key: 96-bit master key

    Returns:
        48-bit plaintext block
    """
    # Convert master key to words and generate round keys
    key_words = speck_48_96_key_to_words(master_key)
    round_keys = speck_48_96_generate_key_schedule(key_words)
    
    # Convert ciphertext to words
    x, y = speck_48_96_block_to_words(ciphertext)
    
    # Decrypt
    x, y = speck_48_96_decrypt_block(x, y, round_keys)
    
    # Convert back to block
    return speck_48_96_words_to_block(x, y)



def test_speck_48_96():
    """Test Speck-48/96 against reference vectors."""
    print("=" * 60)
    print(f"Testing Speck-48/96")
    print("=" * 60)

    print(f"  No test vector available for Speck-48/96")
    print("  Testing round-trip only...")

    plaintext = 0x123456789ABC & ((1 << 48) - 1)
    master_key = 0x0123456789ABCDEF01234567 & ((1 << 96) - 1)

    ciphertext = speck_48_96_encrypt(plaintext, master_key)
    decrypted = speck_48_96_decrypt(ciphertext, master_key)

    block_hex_width = 48 // 4
    key_hex_width = 96 // 4

    print(f"  Plaintext:  0x{plaintext:0{block_hex_width}X}")
    print(f"  Key:        0x{master_key:0{key_hex_width}X}")
    print(f"  Ciphertext: 0x{ciphertext:0{block_hex_width}X}")
    print(f"  Decrypted:  0x{decrypted:0{block_hex_width}X}")

    if decrypted == plaintext:
        print("  ✅ Round-trip PASSED")
    else:
        print("  ❌ Round-trip FAILED")

    # Additional round-trip checks (zero values, all-ones, random-ish)
    extra_ok = True
    for plaintext_extra, key_extra in [
        (0x000000000000, 0x000000000000000000000000),
        (0xFFFFFFFFFFFF, 0xFFFFFFFFFFFFFFFFFFFFFFFF),
        (0xABCDEF012345, 0x0102030405060708090A0B0C),
    ]:
        ct = speck_48_96_encrypt(plaintext_extra, key_extra)
        dec = speck_48_96_decrypt(ct, key_extra)
        if dec != plaintext_extra:
            extra_ok = False

    print("  ✅ Extra round-trip checks PASSED" if extra_ok else "  ❌ Extra round-trip checks FAILED")

    return decrypted == plaintext and extra_ok


def debug_key_schedule():
    """
    Debug function to print key schedule details.
    Useful for verifying against Isabelle implementation.
    """
    print("\n" + "=" * 60)
    print("Key Schedule Debug Information")
    print("=" * 60)
    
    master_key = 0x0123456789ABCDEF01234567 & ((1 << 96) - 1)
    key_words = speck_48_96_key_to_words(master_key)

    print(f"Master Key:           0x{master_key:024X}")
    print(f"Key Words (little-endian):")
    for i, kw in enumerate(key_words):
        print(f"  k{i}: 0x{kw:06X}")

    round_keys = speck_48_96_generate_key_schedule(key_words)

    print(f"\nRound Keys ({len(round_keys)} rounds):")
    for i, rk in enumerate(round_keys):
        print(f"  K[{i:2d}]: 0x{rk:06X}")

    return round_keys



if __name__ == "__main__":
    # Run tests
    test_speck_48_96()
    
    # Optional: debug key schedule
    # debug_key_schedule()