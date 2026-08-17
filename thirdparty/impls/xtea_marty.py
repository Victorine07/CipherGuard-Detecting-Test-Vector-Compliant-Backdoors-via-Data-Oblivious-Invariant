# Third-party XTEA implementation.
# Source: https://github.com/martysama0134/python-tea  (python/xtea.py)
# Python-3 port for the conformance study: the ONLY changes from upstream are mechanical and
# semantics-preserving --- long-literal suffixes were removed from NUMERIC literals
# (e.g. 0x9E3779B9L -> 0x9E3779B9, 0L -> 0), `xrange` was replaced by `range`, and integer
# division `/` was made `//` in xtea_encrypt_all. The struct format strings "2L"/"4L" (two/four
# unsigned longs) are unchanged, as is the cipher logic. Faithfulness is validated by e11
# reproducing the official XTEA test vectors (see src/corpus/conformance.py REFERENCE_VECTORS).

import struct

XTEA_DELTA = 0x9E3779B9
XTEA_N = 32


def xtea_encrypt(block, key, endian="!"):
    """Encrypt one 64-bit block (8 bytes) under a 128-bit key (16 bytes)."""
    (pack, unpack) = (struct.pack, struct.unpack)

    (y, z) = unpack(endian + "2L", block)
    k = unpack(endian + "4L", key)

    global XTEA_DELTA, XTEA_N
    (sum, delta, n) = 0, XTEA_DELTA, XTEA_N

    for i in range(n):
        y = (y + (((z << 4 ^ z >> 5) + z) ^ (sum + k[sum & 3]))) & 0xFFFFFFFF
        sum = (sum + delta) & 0xFFFFFFFF
        z = (z + (((y << 4 ^ y >> 5) + y) ^ (sum + k[sum >> 11 & 3]))) & 0xFFFFFFFF
    return pack(endian + "2L", y, z)


def xtea_decrypt(block, key, endian="!"):
    """Decrypt one 64-bit block (8 bytes) under a 128-bit key (16 bytes)."""
    (pack, unpack) = (struct.pack, struct.unpack)

    (y, z) = unpack(endian + "2L", block)
    k = unpack(endian + "4L", key)

    global XTEA_DELTA, XTEA_N
    (sum, delta, n) = 0, XTEA_DELTA, XTEA_N

    sum = (delta * n) & 0xFFFFFFFF
    for i in range(n):
        z = (z - (((y << 4 ^ y >> 5) + y) ^ (sum + k[sum >> 11 & 3]))) & 0xFFFFFFFF
        sum = (sum - delta) & 0xFFFFFFFF
        y = (y - (((z << 4 ^ z >> 5) + z) ^ (sum + k[sum & 3]))) & 0xFFFFFFFF
    return pack(endian + "2L", y, z)


def xtea_encrypt_all(data, key, endian="!"):
    """Encrypt an entire byte string, zero-padded to the block boundary."""
    newdata = b""
    data_s = len(data)
    data_p = data_s % 8
    if data_p:
        data_pl = 8 - data_p
        data += (data_pl * b"\0")
        data_s += data_pl
    for i in range(data_s // 8):
        block = data[i * 8:(i * 8) + 8]
        newdata += xtea_encrypt(block, key, endian)
    return newdata
