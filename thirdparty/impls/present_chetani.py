# S-Box, Inverse S-Box, and Permutation Table
S = [0xC, 0x5, 0x6, 0xB, 0x9, 0x0, 0xA, 0xD, 0x3, 0xE, 0xF, 0x8, 0x4, 0x7, 0x1, 0x2]
invS = [0x5, 0xE, 0xF, 0x8, 0xC, 0x1, 0x2, 0xD, 0xB, 0x4, 0x6, 0x3, 0x0, 0x7, 0x9, 0xA]
P = [
    0, 16, 32, 48, 1, 17, 33, 49, 2, 18, 34, 50, 3, 19, 35, 51,
    4, 20, 36, 52, 5, 21, 37, 53, 6, 22, 38, 54, 7, 23, 39, 55,
    8, 24, 40, 56, 9, 25, 41, 57, 10, 26, 42, 58, 11, 27, 43, 59,
    12, 28, 44, 60, 13, 29, 45, 61, 14, 30, 46, 62, 15, 31, 47, 63
]

# Helper Functions
def from_hex_to_int(hex_string):
    return int(hex_string, 16)

def from_int_to_hex(value, length=16):
    return f"{value:0{length}x}"

def sbox(input):
    return S[input]

def inverse_sbox(input):
    return invS[input]

# Permutation Functions
def permute(state):
    result = 0
    for i in range(64):
        result |= ((state >> (63 - i)) & 1) << (63 - P[i])
    return result

def inverse_permute(state):
    result = 0
    for i in range(64):
        result |= ((state >> (63 - P[i])) & 1) << (63 - i)
    return result

# Key Schedule
def generate_subkeys(key_hex):
    if len(key_hex) != 20:
        raise ValueError("Key must be 80 bits (20 hexadecimal characters).")
    key = from_hex_to_int(key_hex)
    subkeys = []
    for i in range(32):
        subkeys.append(key >> 16)
        # Rotate key left by 61 bits
        key = ((key << 61) & (2**80 - 1)) | (key >> 19)
        # Apply S-box to the top 4 bits
        top_nibble = (key >> 76) & 0xF
        key = (S[top_nibble] << 76) | (key & (2**76 - 1))
        # XOR round counter
        key ^= i << 15
    return subkeys

# Encryption Function
def encrypt(plaintext_hex, key_hex):
    plaintext = from_hex_to_int(plaintext_hex)
    subkeys = generate_subkeys(key_hex)
    state = plaintext
    for i in range(31):
        state ^= subkeys[i]
        state = sum(S[(state >> (4 * (15 - j))) & 0xF] << (4 * (15 - j)) for j in range(16))
        state = permute(state)
    state ^= subkeys[31]
    return from_int_to_hex(state)

# Decryption Function
def decrypt(ciphertext_hex, key_hex):
    ciphertext = from_hex_to_int(ciphertext_hex)
    subkeys = generate_subkeys(key_hex)
    state = ciphertext
    state ^= subkeys[31]
    for i in range(30, -1, -1):
        state = inverse_permute(state)
        state = sum(invS[(state >> (4 * (15 - j))) & 0xF] << (4 * (15 - j)) for j in range(16))
        state ^= subkeys[i]
    return from_int_to_hex(state)

# Main Program
if __name__ == "__main__":
    key = input("Enter the key (80 bits) in hexadecimal format: ").strip()
    plaintext = input("Enter the plaintext (64 bits) in hexadecimal format: ").strip()
    
    ciphertext = encrypt(plaintext, key)
    print(f"Ciphertext: {ciphertext}")
    
    decrypted_text = decrypt(ciphertext, key)
    print(f"Decrypted Plaintext: {decrypted_text}")
