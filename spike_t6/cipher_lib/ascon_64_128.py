"""
ASCON-64/128 authenticated cipher (Ascon-128: rate=64 bits, key=128 bits).

T1: Constants
T2: Primitives (permutation round: constant, substitution, diffusion)
T3: (none -- ASCON has no key schedule, the key is used directly)
T4: Orchestration (permutation iteration, AEAD building blocks, encrypt/decrypt)

Reference: Dobraunig, Eichlseder, Mendel, Schlaffer, "Ascon v1.2"
(NIST LWC winner; CAESAR portfolio). Algorithm ported from the designers'
own reference implementation (github.com/meichlseder/pyascon, Ascon-128
parameters: a=12, b=6, rate=8 bytes).
"""


KEY_SIZE = 128
NONCE_SIZE = 128
RATE = 64
ROUNDS_A = 12
ROUNDS_B = 6

WORD_MASK = (1 << 64) - 1
RATE_BYTES = RATE // 8


def ascon_64_128_add_round_constant(state: list[int], round_index: int) -> list[int]:
    """Add the round constant for round `round_index` (0..11) to word x2."""
    rc = (0xF0 - round_index * 0x10 + round_index * 0x1) & WORD_MASK
    new_state = state[:]
    new_state[2] ^= rc
    return new_state


def ascon_64_128_substitution_layer(state: list[int]) -> list[int]:
    """The 5-bit S-box, applied bit-sliced across the 5 lanes."""
    s = state[:]
    s[0] ^= s[4]
    s[4] ^= s[3]
    s[2] ^= s[1]
    t = [(s[i] ^ WORD_MASK) & s[(i + 1) % 5] for i in range(5)]
    for i in range(5):
        s[i] ^= t[(i + 1) % 5]
    s[1] ^= s[0]
    s[0] ^= s[4]
    s[3] ^= s[2]
    s[2] ^= WORD_MASK
    return s


def ascon_64_128_linear_diffusion_layer(state: list[int]) -> list[int]:
    """Linear diffusion: each lane XORed with two rotations of itself."""
    def rotr(x: int, r: int) -> int:
        return (x >> r) | ((x << (64 - r)) & WORD_MASK)

    s = state[:]
    s[0] ^= rotr(s[0], 19) ^ rotr(s[0], 28)
    s[1] ^= rotr(s[1], 61) ^ rotr(s[1], 39)
    s[2] ^= rotr(s[2], 1) ^ rotr(s[2], 6)
    s[3] ^= rotr(s[3], 10) ^ rotr(s[3], 17)
    s[4] ^= rotr(s[4], 7) ^ rotr(s[4], 41)
    return s


def ascon_64_128_permutation_round(state: list[int], round_index: int) -> list[int]:
    """One full permutation round: add constant, substitute, diffuse."""
    state = ascon_64_128_add_round_constant(state, round_index)
    state = ascon_64_128_substitution_layer(state)
    state = ascon_64_128_linear_diffusion_layer(state)
    return state


def ascon_64_128_permutation_iterate(state: list[int], round_index: int) -> list[int]:
    """Recursively apply permutation rounds round_index, round_index+1, ..., 11."""
    if round_index >= 12:
        return state
    state = ascon_64_128_permutation_round(state, round_index)
    return ascon_64_128_permutation_iterate(state, round_index + 1)


def ascon_64_128_bytes_to_word(b: bytes) -> int:
    return int.from_bytes(b, "big")


def ascon_64_128_word_to_bytes(x: int, n: int) -> bytes:
    return (x & ((1 << (8 * n)) - 1)).to_bytes(n, "big")


def ascon_64_128_bytes_to_state(b: bytes) -> list[int]:
    return [ascon_64_128_bytes_to_word(b[8 * w:8 * (w + 1)]) for w in range(5)]


def ascon_64_128_pad(data: bytes, block_bytes: int) -> bytes:
    pad_len = block_bytes - (len(data) % block_bytes) - 1
    return data + bytes([0x80]) + bytes(pad_len)


def ascon_64_128_initialize(key: bytes, nonce: bytes) -> list[int]:
    """Load IV||key||nonce into the 320-bit state, run p^a, then absorb the key."""
    iv = bytes([KEY_SIZE, RATE_BYTES * 8, ROUNDS_A, ROUNDS_B]) + bytes(4)
    state = ascon_64_128_bytes_to_state(iv + key + nonce)
    state = ascon_64_128_permutation_iterate(state, 0)

    zero_key_state = ascon_64_128_bytes_to_state(bytes(40 - len(key)) + key)
    return [state[i] ^ zero_key_state[i] for i in range(5)]


def ascon_64_128_absorb_ad_blocks(state: list[int], remaining: bytes) -> list[int]:
    """Recursive accumulator absorbing one rate-sized AD block per step
    (mirrors the Isabelle recursive helper ascon_64_128_absorb_ad_blocks)."""
    if len(remaining) == 0:
        return state
    w0 = ascon_64_128_bytes_to_word(remaining[0:8])
    new_state = state[:]
    new_state[0] ^= w0
    new_state = ascon_64_128_permutation_iterate(new_state, 12 - ROUNDS_B)
    return ascon_64_128_absorb_ad_blocks(new_state, remaining[8:])


def ascon_64_128_process_associated_data(state: list[int], associated_data: bytes) -> list[int]:
    """Absorb padded associated data (rate-sized blocks); no-op if AD is empty."""
    if len(associated_data) > 0:
        padded = ascon_64_128_pad(associated_data, RATE_BYTES)
        new_state = ascon_64_128_absorb_ad_blocks(state, padded)
    else:
        new_state = state[:]
    new_state[4] ^= 1
    return new_state


def ascon_64_128_squeeze_pt_blocks(
    state: list[int], remaining: bytes, p_lastlen: int
) -> tuple[list[int], bytes]:
    """Recursive accumulator absorbing plaintext and squeezing ciphertext
    one rate-sized block per step (mirrors the Isabelle recursive helper
    ascon_64_128_squeeze_pt_blocks)."""
    w0 = ascon_64_128_bytes_to_word(remaining[0:8])
    new_state = state[:]
    new_state[0] ^= w0
    if len(remaining) <= RATE_BYTES:
        return new_state, ascon_64_128_word_to_bytes(new_state[0], 8)[:p_lastlen]
    final_state, rest_ct = ascon_64_128_squeeze_pt_blocks(
        ascon_64_128_permutation_iterate(new_state, 12 - ROUNDS_B), remaining[RATE_BYTES:], p_lastlen
    )
    return final_state, ascon_64_128_word_to_bytes(new_state[0], 8) + rest_ct


def ascon_64_128_process_plaintext(state: list[int], plaintext: bytes) -> tuple[list[int], bytes]:
    """Absorb padded plaintext, squeezing ciphertext blocks; returns (state, ciphertext)."""
    p_lastlen = len(plaintext) % RATE_BYTES
    padded = plaintext + bytes([0x80]) + bytes(RATE_BYTES - p_lastlen - 1)
    return ascon_64_128_squeeze_pt_blocks(state, padded, p_lastlen)


def ascon_64_128_squeeze_ct_blocks(
    state: list[int], remaining: bytes, c_lastlen: int
) -> tuple[list[int], bytes]:
    """Recursive accumulator absorbing ciphertext and squeezing plaintext
    one rate-sized block per step (mirrors the Isabelle recursive helper
    ascon_64_128_squeeze_ct_blocks)."""
    ci = ascon_64_128_bytes_to_word(remaining[0:8])
    if len(remaining) <= RATE_BYTES:
        c_padding1 = 0x80 << ((RATE_BYTES - c_lastlen - 1) * 8)
        c_mask = WORD_MASK >> (c_lastlen * 8)
        pt_block = ascon_64_128_word_to_bytes(ci ^ state[0], 8)[:c_lastlen]
        new_state = state[:]
        new_state[0] = ci ^ (state[0] & c_mask) ^ c_padding1
        return new_state, pt_block
    pt_block = ascon_64_128_word_to_bytes(state[0] ^ ci, 8)
    state1 = state[:]
    state1[0] = ci
    state2 = ascon_64_128_permutation_iterate(state1, 12 - ROUNDS_B)
    final_state, rest_pt = ascon_64_128_squeeze_ct_blocks(state2, remaining[RATE_BYTES:], c_lastlen)
    return final_state, pt_block + rest_pt


def ascon_64_128_process_ciphertext(state: list[int], ciphertext: bytes) -> tuple[list[int], bytes]:
    """Absorb ciphertext blocks, squeezing plaintext; returns (state, plaintext)."""
    c_lastlen = len(ciphertext) % RATE_BYTES
    padded = ciphertext + bytes(RATE_BYTES - c_lastlen)
    return ascon_64_128_squeeze_ct_blocks(state, padded, c_lastlen)


def ascon_64_128_finalize(state: list[int], key: bytes) -> tuple[list[int], bytes]:
    """XOR key into the capacity, run p^a, derive the 128-bit tag from x3,x4."""
    new_state = state[:]
    new_state[1] ^= ascon_64_128_bytes_to_word(key[0:8])
    new_state[2] ^= ascon_64_128_bytes_to_word(key[8:16])
    new_state = ascon_64_128_permutation_iterate(new_state, 0)
    new_state[3] ^= ascon_64_128_bytes_to_word(key[0:8])
    new_state[4] ^= ascon_64_128_bytes_to_word(key[8:16])
    tag = ascon_64_128_word_to_bytes(new_state[3], 8) + ascon_64_128_word_to_bytes(new_state[4], 8)
    return new_state, tag


def ascon_64_128_encrypt(key: bytes, nonce: bytes, associated_data: bytes, plaintext: bytes) -> bytes:
    """Ascon-128 AEAD encryption; returns ciphertext || 128-bit tag."""
    state = ascon_64_128_initialize(key, nonce)
    state = ascon_64_128_process_associated_data(state, associated_data)
    state, ciphertext = ascon_64_128_process_plaintext(state, plaintext)
    _, tag = ascon_64_128_finalize(state, key)
    return ciphertext + tag


def ascon_64_128_decrypt(key: bytes, nonce: bytes, associated_data: bytes, ciphertext: bytes) -> bytes | None:
    """Ascon-128 AEAD decryption; returns plaintext, or None if the tag does not verify."""
    body, tag = ciphertext[:-16], ciphertext[-16:]
    state = ascon_64_128_initialize(key, nonce)
    state = ascon_64_128_process_associated_data(state, associated_data)
    state, plaintext = ascon_64_128_process_ciphertext(state, body)
    _, expected_tag = ascon_64_128_finalize(state, key)
    if expected_tag == tag:
        return plaintext
    return None


def ascon_64_128_test() -> bool:
    """
    Official Ascon-128 KAT-style test vectors (designers' own reference
    implementation, standard NIST LWC KAT key/nonce/AD/PT generation
    scheme: key=nonce=00..0F, AD/PT = sequential bytes 00,01,02,...).
    """
    print("=" * 60)
    print("Testing ASCON-64/128 (Ascon-128)")
    print("=" * 60)

    key = bytes(range(16))
    nonce = bytes(range(16))
    msg32 = bytes(range(32))
    ad32 = bytes(range(32))

    vectors = [
        (0, 0, bytes.fromhex("e355159f292911f794cb1432a0103a8a")),
        (0, 1, bytes.fromhex("944df887cd4901614c5dedbc42fc0da0")),
        (32, 32, bytes.fromhex(
            "b96c78651b6246b0c3b1a5d373b0d5168dca4a96734cf0ddf5f92f8d15e30270279bf6a6cc3f2fc9350b915c292bdb8d"
        )),
    ]

    all_ok = True
    for idx, (plen, adlen, expected_ct) in enumerate(vectors, start=1):
        pt = msg32[:plen]
        ad = ad32[:adlen]
        ct = ascon_64_128_encrypt(key, nonce, ad, pt)
        dec = ascon_64_128_decrypt(key, nonce, ad, ct)
        ok_enc = ct == expected_ct
        ok_dec = dec == pt
        print(f"Test Vector {idx} (|PT|={plen}, |AD|={adlen}):")
        print(f"  Ciphertext+Tag: {ct.hex()}")
        print(f"  Expected:       {expected_ct.hex()}")
        print(f"  Decrypted OK:   {ok_dec}")
        print("  ✅ PASSED" if (ok_enc and ok_dec) else "  ❌ FAILED")
        all_ok = all_ok and ok_enc and ok_dec

    print()
    print("✅ All ASCON-64/128 tests passed!" if all_ok else "❌ ASCON-64/128 TEST FAILURE")
    print("=" * 60)
    return all_ok


if __name__ == "__main__":
    success = ascon_64_128_test()
    if not success:
        raise SystemExit(1)
