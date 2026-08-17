"""
GIFT-COFB authenticated encryption (single-variant, tiered implementation).
COFB (COmbined FeedBack) mode built on the GIFTb-128 permutation.

T1: Constants
T2: Primitives (bitsliced S-box, Galois-field doubling/tripling, G permutation)
T3: Structural Components (key schedule, bundled round function, full permutation)
T4: Orchestration (AD/message processing, rho/rho_prime, encrypt/decrypt)

Reference: Banik, Chakraborti, Iwata, Minematsu, Nandi, Peyrin, Sasaki,
Sim, Todo, "GIFT-COFB", NIST Lightweight Cryptography finalist
(https://www.isical.ac.in/~lightweight/COFB/). Algorithm ported from and
cross-validated against github.com/aadomn/gift's giftb128.c/cofb.h/
encrypt.c (Alexandre Adomnicai, NTU) -- compiled directly via gcc and run
as an oracle to generate the test vectors below. GIFT-COFB uses the
"GIFTb-128" fixsliced bit-ordering of the GIFT-128 permutation, which is
NOT bit-for-bit identical to the standalone GIFT-128 cipher already in
this dataset (gift_128_128.py) -- confirmed by direct comparison; see
references/gift_cofb.md for details and the naming-correction rationale
("64/128" in the task list does not correspond to any real GIFT-COFB
parameter; the real cipher has key = nonce = tag = 128 bits).
"""


from typing import Optional

M32 = 0xFFFFFFFF
BLOCK_SIZE = 128
KEY_SIZE = 128
NONCE_SIZE = 128
TAG_SIZE = 128
ROUNDS = 40
BLOCKBYTES = 16

RCONST = [
    0x10000008, 0x80018000, 0x54000002, 0x01010181,
    0x8000001f, 0x10888880, 0x6001e000, 0x51500002,
    0x03030180, 0x8000002f, 0x10088880, 0x60016000,
    0x41500002, 0x03030080, 0x80000027, 0x10008880,
    0x4001e000, 0x11500002, 0x03020180, 0x8000002b,
    0x10080880, 0x60014000, 0x01400002, 0x02020080,
    0x80000021, 0x10000080, 0x0001c000, 0x51000002,
    0x03010180, 0x8000002e, 0x10088800, 0x60012000,
    0x40500002, 0x01030080, 0x80000006, 0x10008808,
    0xc001a000, 0x14500002, 0x01020181, 0x8000001a,
]


def gift_cofb_128_128_ror32(x, y):
    return ((x >> y) | (x << (32 - y))) & M32


def gift_cofb_128_128_swapmove_self(v, mask, n):
    tmp = (v ^ (v >> n)) & mask
    v = (v ^ tmp) & M32
    v = (v ^ ((tmp << n) & M32)) & M32
    return v


def gift_cofb_128_128_sbox(s0: int, s1: int, s2: int, s3: int) -> tuple[int, int, int, int]:
    """Bitsliced 4-input boolean S-box step shared by every quarter-round."""
    s1 = s1 ^ (s0 & s2)
    s0 = s0 ^ (s1 & s3)
    s2 = s2 ^ (s0 | s1)
    s3 = s3 ^ s2
    s1 = s1 ^ s3
    s3 = s3 ^ M32
    s2 = s2 ^ (s0 & s1)
    return s0 & M32, s1 & M32, s2 & M32, s3 & M32


def gift_cofb_128_128_double_half_block(offset: bytes) -> bytes:
    """Double a 64-bit offset over GF(2^8)^8 (byte-parallel xtime + LFSR carry)."""
    x0 = int.from_bytes(offset[0:4], "little")
    x1 = int.from_bytes(offset[4:8], "little")
    new_x0 = ((((x0 & 0x7f7f7f7f) << 1) | ((x0 & 0x80808080) >> 15)) | (((x1 & 0x80808080) << 17) & M32)) & M32
    new_x1 = ((((x1 & 0x7f7f7f7f) << 1) | ((x1 & 0x80808080) >> 15)) ^ ((((x0 >> 7) & 1) * 27) << 24)) & M32
    return new_x0.to_bytes(4, "little") + new_x1.to_bytes(4, "little")


def gift_cofb_128_128_triple_half_block(offset: bytes) -> bytes:
    """Triple a 64-bit offset (double then XOR the original, i.e. 3x = 2x ^ x)."""
    doubled = gift_cofb_128_128_double_half_block(offset)
    return bytes(a ^ b for a, b in zip(doubled, offset))


def gift_cofb_128_128_g_function(y: bytes) -> bytes:
    """G(Y): rotate Y's two halves and double-without-carry-XOR the vacated half."""
    tmp0 = int.from_bytes(y[0:4], "little")
    tmp1 = int.from_bytes(y[4:8], "little")
    new_y2 = ((((tmp0 & 0x7f7f7f7f) << 1) | ((tmp0 & 0x80808080) >> 15)) | (((tmp1 & 0x80808080) << 17) & M32)) & M32
    new_y3 = ((((tmp1 & 0x7f7f7f7f) << 1) | ((tmp1 & 0x80808080) >> 15)) | (((tmp0 & 0x80808080) << 17) & M32)) & M32
    return y[8:12] + y[12:16] + new_y2.to_bytes(4, "little") + new_y3.to_bytes(4, "little")


# ----------------------------------------------------------------------
# T3: Structural Components (GIFTb-128 key schedule + permutation)
# ----------------------------------------------------------------------

def gift_cofb_128_128_key_update(x: int) -> int:
    return (((x >> 12) & 0x0000000f) | ((x & 0x00000fff) << 4) |
            ((x >> 2) & 0x3fff0000) | ((x & 0x00030000) << 14)) & M32


def gift_cofb_128_128_rearrange_rkey_0(x: int) -> int:
    x = gift_cofb_128_128_swapmove_self(x, 0x00550055, 9)
    x = gift_cofb_128_128_swapmove_self(x, 0x000f000f, 12)
    x = gift_cofb_128_128_swapmove_self(x, 0x00003333, 18)
    x = gift_cofb_128_128_swapmove_self(x, 0x000000ff, 24)
    return x


def gift_cofb_128_128_rearrange_rkey_1(x: int) -> int:
    x = gift_cofb_128_128_swapmove_self(x, 0x11111111, 3)
    x = gift_cofb_128_128_swapmove_self(x, 0x03030303, 6)
    x = gift_cofb_128_128_swapmove_self(x, 0x000f000f, 12)
    x = gift_cofb_128_128_swapmove_self(x, 0x000000ff, 24)
    return x


def gift_cofb_128_128_rearrange_rkey_2(x: int) -> int:
    x = gift_cofb_128_128_swapmove_self(x, 0x0000aaaa, 15)
    x = gift_cofb_128_128_swapmove_self(x, 0x00003333, 18)
    x = gift_cofb_128_128_swapmove_self(x, 0x0000f0f0, 12)
    x = gift_cofb_128_128_swapmove_self(x, 0x000000ff, 24)
    return x


def gift_cofb_128_128_rearrange_rkey_3(x: int) -> int:
    x = gift_cofb_128_128_swapmove_self(x, 0x0a0a0a0a, 3)
    x = gift_cofb_128_128_swapmove_self(x, 0x00cc00cc, 6)
    x = gift_cofb_128_128_swapmove_self(x, 0x0000f0f0, 12)
    x = gift_cofb_128_128_swapmove_self(x, 0x000000ff, 24)
    return x


def gift_cofb_128_128_key_triple_update_0(x: int) -> int:
    return (gift_cofb_128_128_ror32(x & 0x33333333, 24) | gift_cofb_128_128_ror32(x & 0xcccccccc, 16)) & M32


def gift_cofb_128_128_key_double_update_1(x: int) -> int:
    return (((x >> 4) & 0x0f000f00) | ((x & 0x0f000f00) << 4) |
            ((x >> 6) & 0x00030003) | ((x & 0x003f003f) << 2)) & M32


def gift_cofb_128_128_key_triple_update_1(x: int) -> int:
    return (((x >> 6) & 0x03000300) | ((x & 0x3f003f00) << 2) |
            ((x >> 5) & 0x00070007) | ((x & 0x001f001f) << 3)) & M32


def gift_cofb_128_128_key_double_update_2(x: int) -> int:
    return (gift_cofb_128_128_ror32(x & 0xaaaaaaaa, 24) | gift_cofb_128_128_ror32(x & 0x55555555, 16)) & M32


def gift_cofb_128_128_key_triple_update_2(x: int) -> int:
    return (gift_cofb_128_128_ror32(x & 0x55555555, 24) | gift_cofb_128_128_ror32(x & 0xaaaaaaaa, 20)) & M32


def gift_cofb_128_128_key_double_update_3(x: int) -> int:
    return (((x >> 2) & 0x03030303) | ((x & 0x03030303) << 2) |
            ((x >> 1) & 0x70707070) | ((x & 0x10101010) << 3)) & M32


def gift_cofb_128_128_key_triple_update_3(x: int) -> int:
    return (((x >> 18) & 0x00003030) | ((x & 0x01010101) << 3) |
            ((x >> 14) & 0x0000c0c0) | ((x & 0x0000e0e0) << 15) |
            ((x >> 1) & 0x07070707) | ((x & 0x00001010) << 19)) & M32


def gift_cofb_128_128_key_double_update_4(x: int) -> int:
    return (((x >> 4) & 0x0fff0000) | ((x & 0x000f0000) << 12) |
            ((x >> 8) & 0x000000ff) | ((x & 0x000000ff) << 8)) & M32


def gift_cofb_128_128_key_triple_update_4(x: int) -> int:
    return (((x >> 6) & 0x03ff0000) | ((x & 0x003f0000) << 10) |
            ((x >> 4) & 0x00000fff) | ((x & 0x0000000f) << 12)) & M32


def gift_cofb_128_128_phase4_step(rkey: list[int], i: int) -> list[int]:
    """One phase-4 key-schedule step at position i (mirrors the Isabelle
    definition gift_cofb_128_128_phase4_step)."""
    v0 = gift_cofb_128_128_key_triple_update_0(rkey[i - 20])
    v1 = gift_cofb_128_128_key_double_update_1(rkey[i - 17])
    v2 = gift_cofb_128_128_key_triple_update_1(rkey[i - 18])
    v3 = gift_cofb_128_128_key_double_update_2(rkey[i - 15])
    v4 = gift_cofb_128_128_key_triple_update_2(rkey[i - 16])
    v5 = gift_cofb_128_128_key_double_update_3(rkey[i - 13])
    v6 = gift_cofb_128_128_key_triple_update_3(rkey[i - 14])
    v7 = gift_cofb_128_128_key_double_update_4(rkey[i - 11])
    v8 = gift_cofb_128_128_key_triple_update_4(rkey[i - 12])
    base = rkey[i - 19]
    rkey_a = list(rkey)
    rkey_a[i:i + 10] = [base, v0, v1, v2, v3, v4, v5, v6, v7, v8]
    rkey_a[i] = gift_cofb_128_128_swapmove_self(rkey_a[i], 0x00003333, 16)
    rkey_a[i] = gift_cofb_128_128_swapmove_self(rkey_a[i], 0x55554444, 1)
    rkey_a[i + 1] = gift_cofb_128_128_swapmove_self(rkey_a[i + 1], 0x55551100, 1)
    return rkey_a


def gift_cofb_128_128_precompute_round_keys(key: bytes) -> list[int]:
    """Expand the 128-bit key into 80 fixsliced round-key words."""
    words = [int.from_bytes(key[4 * i:4 * i + 4], "big") for i in range(4)]
    rkey = [0] * 80
    rkey[0], rkey[1], rkey[2], rkey[3] = words[3], words[1], words[2], words[0]

    for i in range(0, 16, 2):
        rkey[i + 4] = rkey[i + 1]
        rkey[i + 5] = gift_cofb_128_128_key_update(rkey[i])

    for i in range(0, 20, 10):
        rkey[i] = gift_cofb_128_128_rearrange_rkey_0(rkey[i])
        rkey[i + 1] = gift_cofb_128_128_rearrange_rkey_0(rkey[i + 1])
        rkey[i + 2] = gift_cofb_128_128_rearrange_rkey_1(rkey[i + 2])
        rkey[i + 3] = gift_cofb_128_128_rearrange_rkey_1(rkey[i + 3])
        rkey[i + 4] = gift_cofb_128_128_rearrange_rkey_2(rkey[i + 4])
        rkey[i + 5] = gift_cofb_128_128_rearrange_rkey_2(rkey[i + 5])
        rkey[i + 6] = gift_cofb_128_128_rearrange_rkey_3(rkey[i + 6])
        rkey[i + 7] = gift_cofb_128_128_rearrange_rkey_3(rkey[i + 7])

    rkey = gift_cofb_128_128_phase4_step(rkey, 20)
    rkey = gift_cofb_128_128_phase4_step(rkey, 30)
    rkey = gift_cofb_128_128_phase4_step(rkey, 40)
    rkey = gift_cofb_128_128_phase4_step(rkey, 50)
    rkey = gift_cofb_128_128_phase4_step(rkey, 60)
    rkey = gift_cofb_128_128_phase4_step(rkey, 70)

    return rkey


def gift_cofb_128_128_quintuple_round(state: list[int], rkey: list[int], rconst: list[int]) -> list[int]:
    """Five fixsliced GIFTb-128 rounds bundled into one optimized step."""
    s0, s1, s2, s3 = state
    s0, s1, s2, s3 = gift_cofb_128_128_sbox(s0, s1, s2, s3)
    s3 = (((s3 >> 1) & 0x77777777) | ((s3 & 0x11111111) << 3)) & M32
    s1 = (((s1 >> 2) & 0x33333333) | ((s1 & 0x33333333) << 2)) & M32
    s2 = (((s2 >> 3) & 0x11111111) | ((s2 & 0x77777777) << 1)) & M32
    s1 ^= rkey[0]
    s2 ^= rkey[1]
    s0 ^= rconst[0]

    s3, s1, s2, s0 = gift_cofb_128_128_sbox(s3, s1, s2, s0)
    s0 = (((s0 >> 4) & 0x0fff0fff) | ((s0 & 0x000f000f) << 12)) & M32
    s1 = (((s1 >> 8) & 0x00ff00ff) | ((s1 & 0x00ff00ff) << 8)) & M32
    s2 = (((s2 >> 12) & 0x000f000f) | ((s2 & 0x0fff0fff) << 4)) & M32
    s1 ^= rkey[2]
    s2 ^= rkey[3]
    s3 ^= rconst[1]

    s0, s1, s2, s3 = gift_cofb_128_128_sbox(s0, s1, s2, s3)
    s3 = gift_cofb_128_128_ror32(s3, 16)
    s2 = gift_cofb_128_128_ror32(s2, 16)
    s1 = gift_cofb_128_128_swapmove_self(s1, 0x55555555, 1)
    s2 = gift_cofb_128_128_swapmove_self(s2, 0x00005555, 1)
    s3 = gift_cofb_128_128_swapmove_self(s3, 0x55550000, 1)
    s1 ^= rkey[4]
    s2 ^= rkey[5]
    s0 ^= rconst[2]

    s3, s1, s2, s0 = gift_cofb_128_128_sbox(s3, s1, s2, s0)
    s0 = (((s0 >> 6) & 0x03030303) | ((s0 & 0x3f3f3f3f) << 2)) & M32
    s1 = (((s1 >> 4) & 0x0f0f0f0f) | ((s1 & 0x0f0f0f0f) << 4)) & M32
    s2 = (((s2 >> 2) & 0x3f3f3f3f) | ((s2 & 0x03030303) << 6)) & M32
    s1 ^= rkey[6]
    s2 ^= rkey[7]
    s3 ^= rconst[3]

    s0, s1, s2, s3 = gift_cofb_128_128_sbox(s0, s1, s2, s3)
    s3 = gift_cofb_128_128_ror32(s3, 24)
    s1 = gift_cofb_128_128_ror32(s1, 16)
    s2 = gift_cofb_128_128_ror32(s2, 8)
    s1 ^= rkey[8]
    s2 ^= rkey[9]
    s0 ^= rconst[4]
    s0 ^= s3
    s3 ^= s0
    s0 ^= s3
    return [s0 & M32, s1 & M32, s2 & M32, s3 & M32]


def gift_cofb_128_128_permutation(block: bytes, rkey: list[int]) -> bytes:
    """Full 40-round GIFTb-128 permutation (8 quintuple-rounds)."""
    state = [int.from_bytes(block[4 * i:4 * i + 4], "big") for i in range(4)]
    for r in range(8):
        state = gift_cofb_128_128_quintuple_round(state, rkey[r * 10:r * 10 + 10], RCONST[r * 5:r * 5 + 5])
    return b"".join(s.to_bytes(4, "big") for s in state)


# ----------------------------------------------------------------------
# T4: Orchestration (COFB mode)
# ----------------------------------------------------------------------

def gift_cofb_128_128_padding(data: bytes, n: int) -> bytes:
    """Pad data's first n real bytes to a full 16-byte block (0x80 marker + zeros)."""
    if n >= BLOCKBYTES:
        return data[:BLOCKBYTES]
    return data[:n] + bytes([0x80]) + bytes(BLOCKBYTES - n - 1)


def gift_cofb_128_128_initialize(key: bytes, nonce: bytes) -> tuple[bytes, bytes, list[int]]:
    """Derive the initial state Y = E_K(N) and offset = top 64 bits of Y."""
    rkey = gift_cofb_128_128_precompute_round_keys(key)
    y = gift_cofb_128_128_permutation(nonce, rkey)
    offset = y[0:8]
    return y, offset, rkey


def gift_cofb_128_128_process_ad_blocks_loop(
    ad: bytes, y: bytes, offset: bytes, rkey: list[int]
) -> tuple[bytes, bytes, bytes]:
    """Recursive accumulator absorbing one full AD block per step (mirrors
    the Isabelle recursive helper gift_cofb_128_128_process_ad_blocks_loop)."""
    if len(ad) <= BLOCKBYTES:
        return ad, y, offset
    block = ad[:BLOCKBYTES]
    g_y = gift_cofb_128_128_g_function(y)
    input0 = bytes(a ^ b for a, b in zip(gift_cofb_128_128_padding(block, BLOCKBYTES), g_y))
    offset2 = gift_cofb_128_128_double_half_block(offset)
    input1 = bytes(a ^ b for a, b in zip(input0[:8], offset2)) + input0[8:]
    y2 = gift_cofb_128_128_permutation(input1, rkey)
    return gift_cofb_128_128_process_ad_blocks_loop(ad[BLOCKBYTES:], y2, offset2, rkey)


def gift_cofb_128_128_process_associated_data(
    ad: bytes, y: bytes, offset: bytes, rkey: list[int], empty_m: bool
) -> tuple[bytes, bytes, bytes]:
    """Absorb associated data into (Y, offset), block by block, COFB-style."""
    ad_rem, y2, offset2 = gift_cofb_128_128_process_ad_blocks_loop(ad, y, offset, rkey)
    empty_a = len(ad) == 0

    offset3 = gift_cofb_128_128_triple_half_block(offset2)
    if (len(ad_rem) % BLOCKBYTES != 0) or empty_a:
        offset3 = gift_cofb_128_128_triple_half_block(offset3)
    if empty_m:
        offset3 = gift_cofb_128_128_triple_half_block(offset3)
        offset3 = gift_cofb_128_128_triple_half_block(offset3)

    return y2, offset3, ad_rem


def gift_cofb_128_128_encrypt_blocks_loop(
    msg: bytes, y: bytes, offset: bytes, rkey: list[int]
) -> tuple[bytes, bytes, bytes]:
    """Recursive accumulator absorbing one full message block per step,
    encryption direction (mirrors the Isabelle recursive helper
    gift_cofb_128_128_encrypt_blocks_loop)."""
    if len(msg) <= BLOCKBYTES:
        return b"", y, offset
    block = msg[:BLOCKBYTES]
    c_block = bytes(a ^ b for a, b in zip(y, block))
    offset2 = gift_cofb_128_128_double_half_block(offset)
    g_y = gift_cofb_128_128_g_function(y)
    input0 = bytes(a ^ b for a, b in zip(gift_cofb_128_128_padding(block, BLOCKBYTES), g_y))
    input1 = bytes(a ^ b for a, b in zip(input0[:8], offset2)) + input0[8:]
    y2 = gift_cofb_128_128_permutation(input1, rkey)
    rest_ct, y3, offset3 = gift_cofb_128_128_encrypt_blocks_loop(msg[BLOCKBYTES:], y2, offset2, rkey)
    return c_block + rest_ct, y3, offset3


def gift_cofb_128_128_encrypt_message_blocks(
    message: bytes, y: bytes, offset: bytes, rkey: list[int]
) -> tuple[bytes, bytes, bytes]:
    """RHO over the message in the encryption direction: produces ciphertext."""
    ciphertext, y, offset = gift_cofb_128_128_encrypt_blocks_loop(message, y, offset, rkey)

    if message:
        in_len = len(message) - ((len(message) - 1) // BLOCKBYTES) * BLOCKBYTES
        last_block = message[len(message) - in_len:]
        offset = gift_cofb_128_128_triple_half_block(offset)
        if in_len % BLOCKBYTES != 0:
            offset = gift_cofb_128_128_triple_half_block(offset)
        ciphertext += bytes(a ^ b for a, b in zip(y[:in_len], last_block))
        g_y = gift_cofb_128_128_g_function(y)
        input_ = bytes(a ^ b for a, b in zip(gift_cofb_128_128_padding(last_block, in_len), g_y))
        input_ = bytes(a ^ b for a, b in zip(input_[:8], offset)) + input_[8:]
        y = gift_cofb_128_128_permutation(input_, rkey)

    return ciphertext, y, y[:TAG_SIZE // 8]


def gift_cofb_128_128_decrypt_blocks_loop(
    ct: bytes, y: bytes, offset: bytes, rkey: list[int]
) -> tuple[bytes, bytes, bytes]:
    """Recursive accumulator absorbing one full ciphertext block per step,
    decryption direction (mirrors the Isabelle recursive helper
    gift_cofb_128_128_decrypt_blocks_loop)."""
    if len(ct) <= BLOCKBYTES:
        return b"", y, offset
    block = ct[:BLOCKBYTES]
    m_block = bytes(a ^ b for a, b in zip(y, block))
    offset2 = gift_cofb_128_128_double_half_block(offset)
    g_y = gift_cofb_128_128_g_function(y)
    input0 = bytes(a ^ b for a, b in zip(gift_cofb_128_128_padding(m_block, BLOCKBYTES), g_y))
    input1 = bytes(a ^ b for a, b in zip(input0[:8], offset2)) + input0[8:]
    y2 = gift_cofb_128_128_permutation(input1, rkey)
    rest_pt, y3, offset3 = gift_cofb_128_128_decrypt_blocks_loop(ct[BLOCKBYTES:], y2, offset2, rkey)
    return m_block + rest_pt, y3, offset3


def gift_cofb_128_128_decrypt_message_blocks(
    ciphertext: bytes, y: bytes, offset: bytes, rkey: list[int]
) -> tuple[bytes, bytes, bytes]:
    """RHO_PRIME over the ciphertext in the decryption direction: recovers plaintext."""
    plaintext, y, offset = gift_cofb_128_128_decrypt_blocks_loop(ciphertext, y, offset, rkey)

    if ciphertext:
        in_len = len(ciphertext) - ((len(ciphertext) - 1) // BLOCKBYTES) * BLOCKBYTES
        last_block = ciphertext[len(ciphertext) - in_len:]
        offset = gift_cofb_128_128_triple_half_block(offset)
        if in_len % BLOCKBYTES != 0:
            offset = gift_cofb_128_128_triple_half_block(offset)
        m_block = bytes(a ^ b for a, b in zip(y[:in_len], last_block))
        plaintext += m_block
        g_y = gift_cofb_128_128_g_function(y)
        input_ = bytes(a ^ b for a, b in zip(gift_cofb_128_128_padding(m_block, in_len), g_y))
        input_ = bytes(a ^ b for a, b in zip(input_[:8], offset)) + input_[8:]
        y = gift_cofb_128_128_permutation(input_, rkey)

    return plaintext, y, y[:TAG_SIZE // 8]


def gift_cofb_128_128_encrypt(key: bytes, nonce: bytes, ad: bytes, plaintext: bytes) -> bytes:
    """Top-level GIFT-COFB authenticated encryption: returns ciphertext || tag."""
    y, offset, rkey = gift_cofb_128_128_initialize(key, nonce)
    y, offset, ad_remaining = gift_cofb_128_128_process_associated_data(
        ad, y, offset, rkey, empty_m=not plaintext
    )

    g_y = gift_cofb_128_128_g_function(y)
    input_ = bytes(a ^ b for a, b in zip(gift_cofb_128_128_padding(ad_remaining, len(ad_remaining)), g_y))
    input_ = bytes(a ^ b for a, b in zip(input_[:8], offset)) + input_[8:]
    y = gift_cofb_128_128_permutation(input_, rkey)

    if not plaintext:
        return y[:TAG_SIZE // 8]

    ciphertext, y, tag = gift_cofb_128_128_encrypt_message_blocks(plaintext, y, offset, rkey)
    return ciphertext + tag


def gift_cofb_128_128_decrypt(key: bytes, nonce: bytes, ad: bytes, ciphertext: bytes) -> Optional[bytes]:
    """Top-level GIFT-COFB authenticated decryption: returns plaintext, or None if the tag fails."""
    tag = ciphertext[-(TAG_SIZE // 8):]
    body = ciphertext[:-(TAG_SIZE // 8)]

    y, offset, rkey = gift_cofb_128_128_initialize(key, nonce)
    y, offset, ad_remaining = gift_cofb_128_128_process_associated_data(
        ad, y, offset, rkey, empty_m=not body
    )

    g_y = gift_cofb_128_128_g_function(y)
    input_ = bytes(a ^ b for a, b in zip(gift_cofb_128_128_padding(ad_remaining, len(ad_remaining)), g_y))
    input_ = bytes(a ^ b for a, b in zip(input_[:8], offset)) + input_[8:]
    y = gift_cofb_128_128_permutation(input_, rkey)

    if not body:
        expected_tag = y[:TAG_SIZE // 8]
        return b"" if expected_tag == tag else None

    plaintext, y, expected_tag = gift_cofb_128_128_decrypt_message_blocks(body, y, offset, rkey)
    return plaintext if expected_tag == tag else None


def gift_cofb_128_128_test() -> bool:
    """GIFT-COFB test vectors generated from a cross-validated independent reference
    (aadomn/gift, compiled and run as an oracle; see references/gift_cofb.md)."""
    print("=" * 60)
    print("Testing GIFT-COFB-128/128")
    print("=" * 60)

    key = bytes(range(16))
    nonce = bytes(range(16))
    msg32 = bytes(range(32))
    ad32 = bytes(range(32))

    vectors = [
        (0, 0, "368965836d36614de2fc24d0f801b9af"),
        (0, 1, "ae5dcdd1285d5177fe251deb99d727dc"),
        (1, 0, "5df96db329e92688242ef4e06f94fe1bd9"),
        (16, 16, "3bff715a56cba49d1f7ac0691a966fdcbf77814044bf3fc9a9debbd393f545d4"),
        (32, 32, "baf563c60fbeddc5662995f4c678be80a7f7de9b3ad8c97aa6ca17016d2ae6508e6fb3f79b412a1627ab7dfa755e0a22"),
        (5, 3, "4acac27bdcc430b04231b4cb7a92935c83889152dc"),
        (17, 9, "fc4099b87e0bd6c76bbea0eb9850af5d785ae2231e628013df9d4f0f43f436a601"),
    ]

    all_ok = True
    for idx, (mlen, adlen, expected_hex) in enumerate(vectors, start=1):
        pt = msg32[:mlen]
        ad = ad32[:adlen]
        ct = gift_cofb_128_128_encrypt(key, nonce, ad, pt)
        dec = gift_cofb_128_128_decrypt(key, nonce, ad, ct)
        ok_enc = ct.hex() == expected_hex
        ok_dec = dec == pt
        print(f"Test Vector {idx} (mlen={mlen}, adlen={adlen}):")
        print(f"  Ciphertext+Tag: {ct.hex()}")
        print(f"  Expected:       {expected_hex}")
        print(f"  Decrypted matches plaintext: {ok_dec}")
        print("  ✅ PASSED" if (ok_enc and ok_dec) else "  ❌ FAILED")
        all_ok = all_ok and ok_enc and ok_dec

    print()
    print("✅ All GIFT-COFB-128/128 tests passed!" if all_ok else "❌ GIFT-COFB-128/128 TEST FAILURE")
    print("=" * 60)
    return all_ok


if __name__ == "__main__":
    success = gift_cofb_128_128_test()
    if not success:
        raise SystemExit(1)
