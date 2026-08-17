theory Gift_128_128
  imports
    "HOL-Library.Word"
    "HOL.Bit_Operations"
begin

section \<open>GIFT-128/128: Tiered Core Definitions\<close>

subsection \<open>T1: Constants\<close>

definition gift_128_128_block_size :: nat where
  "gift_128_128_block_size = 128"

definition gift_128_128_key_size :: nat where
  "gift_128_128_key_size = 128"

definition gift_128_128_rounds :: nat where
  "gift_128_128_rounds = 40"

definition gift_128_128_sbox :: "4 word list" where
  "gift_128_128_sbox = [1, 10, 4, 12, 6, 15, 3, 9, 2, 13, 11, 7, 5, 0, 8, 14]"

definition gift_128_128_pbox :: "nat list" where
  "gift_128_128_pbox =
     [0, 33, 66, 99, 96, 1, 34, 67, 64, 97, 2, 35, 32, 65, 98, 3,
      4, 37, 70, 103, 100, 5, 38, 71, 68, 101, 6, 39, 36, 69, 102, 7,
      8, 41, 74, 107, 104, 9, 42, 75, 72, 105, 10, 43, 40, 73, 106, 11,
      12, 45, 78, 111, 108, 13, 46, 79, 76, 109, 14, 47, 44, 77, 110, 15,
      16, 49, 82, 115, 112, 17, 50, 83, 80, 113, 18, 51, 48, 81, 114, 19,
      20, 53, 86, 119, 116, 21, 54, 87, 84, 117, 22, 55, 52, 85, 118, 23,
      24, 57, 90, 123, 120, 25, 58, 91, 88, 121, 26, 59, 56, 89, 122, 27,
      28, 61, 94, 127, 124, 29, 62, 95, 92, 125, 30, 63, 60, 93, 126, 31]"

definition gift_128_128_rc :: "nat list" where
  "gift_128_128_rc =
     [0x01, 0x03, 0x07, 0x0F, 0x1F, 0x3E, 0x3D, 0x3B, 0x37, 0x2F,
      0x1E, 0x3C, 0x39, 0x33, 0x27, 0x0E, 0x1D, 0x3A, 0x35, 0x2B,
      0x16, 0x2C, 0x18, 0x30, 0x21, 0x02, 0x05, 0x0B, 0x17, 0x2E,
      0x1C, 0x38, 0x31, 0x23, 0x06, 0x0D, 0x1B, 0x36, 0x2D, 0x1A,
      0x34, 0x29, 0x12, 0x24, 0x08, 0x11, 0x22, 0x04, 0x09, 0x13,
      0x26, 0x0C, 0x19, 0x32, 0x25, 0x0A, 0x15, 0x2A, 0x14, 0x28,
      0x10, 0x20]"

text \<open>Derived inverse tables (not independently specified by the cipher).\<close>

definition gift_128_128_sbox_inv :: "4 word list" where
  "gift_128_128_sbox_inv = [13, 0, 8, 6, 2, 12, 4, 11, 14, 7, 1, 10, 3, 9, 15, 5]"

definition gift_128_128_pbox_inv :: "nat list" where
  "gift_128_128_pbox_inv =
     [0, 5, 10, 15, 16, 21, 26, 31, 32, 37, 42, 47, 48, 53, 58, 63,
      64, 69, 74, 79, 80, 85, 90, 95, 96, 101, 106, 111, 112, 117, 122, 127,
      12, 1, 6, 11, 28, 17, 22, 27, 44, 33, 38, 43, 60, 49, 54, 59,
      76, 65, 70, 75, 92, 81, 86, 91, 108, 97, 102, 107, 124, 113, 118, 123,
      8, 13, 2, 7, 24, 29, 18, 23, 40, 45, 34, 39, 56, 61, 50, 55,
      72, 77, 66, 71, 88, 93, 82, 87, 104, 109, 98, 103, 120, 125, 114, 119,
      4, 9, 14, 3, 20, 25, 30, 19, 36, 41, 46, 35, 52, 57, 62, 51,
      68, 73, 78, 67, 84, 89, 94, 83, 100, 105, 110, 99, 116, 121, 126, 115]"


subsection \<open>T2: Primitives\<close>

function gift_128_128_sbox_layer_acc :: "128 word \<Rightarrow> nat \<Rightarrow> 128 word \<Rightarrow> 128 word" where
  "gift_128_128_sbox_layer_acc state i acc =
     (if i \<ge> 32 then acc
      else
        let nibble = ucast (drop_bit (4 * i) state) :: 4 word;
            sboxed = gift_128_128_sbox ! unat nibble;
            placed = push_bit (4 * i) (ucast sboxed :: 128 word)
        in gift_128_128_sbox_layer_acc state (i + 1) (or acc placed))"
  by pat_completeness auto

termination gift_128_128_sbox_layer_acc
  by (relation "measure (\<lambda>(state, i, acc). 32 - i)") auto

definition gift_128_128_sbox_layer :: "128 word \<Rightarrow> 128 word" where
  "gift_128_128_sbox_layer state = gift_128_128_sbox_layer_acc state 0 0"

function gift_128_128_sbox_layer_inv_acc :: "128 word \<Rightarrow> nat \<Rightarrow> 128 word \<Rightarrow> 128 word" where
  "gift_128_128_sbox_layer_inv_acc state i acc =
     (if i \<ge> 32 then acc
      else
        let nibble = ucast (drop_bit (4 * i) state) :: 4 word;
            sboxed = gift_128_128_sbox_inv ! unat nibble;
            placed = push_bit (4 * i) (ucast sboxed :: 128 word)
        in gift_128_128_sbox_layer_inv_acc state (i + 1) (or acc placed))"
  by pat_completeness auto

termination gift_128_128_sbox_layer_inv_acc
  by (relation "measure (\<lambda>(state, i, acc). 32 - i)") auto

definition gift_128_128_sbox_layer_inv :: "128 word \<Rightarrow> 128 word" where
  "gift_128_128_sbox_layer_inv state = gift_128_128_sbox_layer_inv_acc state 0 0"

function gift_128_128_permutation_layer_acc :: "128 word \<Rightarrow> nat \<Rightarrow> 128 word \<Rightarrow> 128 word" where
  "gift_128_128_permutation_layer_acc state i acc =
     (if i \<ge> 128 then acc
      else
        let bit_val = (if bit state i then (1 :: 128 word) else 0);
            target = gift_128_128_pbox ! i;
            placed = push_bit target bit_val
        in gift_128_128_permutation_layer_acc state (i + 1) (or acc placed))"
  by pat_completeness auto

termination gift_128_128_permutation_layer_acc
  by (relation "measure (\<lambda>(state, i, acc). 128 - i)") auto

definition gift_128_128_permutation_layer :: "128 word \<Rightarrow> 128 word" where
  "gift_128_128_permutation_layer state = gift_128_128_permutation_layer_acc state 0 0"

function gift_128_128_permutation_layer_inv_acc :: "128 word \<Rightarrow> nat \<Rightarrow> 128 word \<Rightarrow> 128 word" where
  "gift_128_128_permutation_layer_inv_acc state i acc =
     (if i \<ge> 128 then acc
      else
        let bit_val = (if bit state i then (1 :: 128 word) else 0);
            target = gift_128_128_pbox_inv ! i;
            placed = push_bit target bit_val
        in gift_128_128_permutation_layer_inv_acc state (i + 1) (or acc placed))"
  by pat_completeness auto

termination gift_128_128_permutation_layer_inv_acc
  by (relation "measure (\<lambda>(state, i, acc). 128 - i)") auto

definition gift_128_128_permutation_layer_inv :: "128 word \<Rightarrow> 128 word" where
  "gift_128_128_permutation_layer_inv state = gift_128_128_permutation_layer_inv_acc state 0 0"


subsection \<open>T3: Structural Components (Key schedule)\<close>

definition gift_128_128_update_key_state :: "4 word list \<Rightarrow> 4 word list" where
  "gift_128_128_update_key_state key_nibbles =
     (let temp = map (\<lambda>i. key_nibbles ! ((i + 8) mod 32)) [0..<32];
          s1 = temp[24 := temp ! 27, 25 := temp ! 24, 26 := temp ! 25, 27 := temp ! 26];
          n28 = or (drop_bit 2 (and (temp ! 28) 0xC)) (push_bit 2 (and (temp ! 29) 0x3));
          n29 = or (drop_bit 2 (and (temp ! 29) 0xC)) (push_bit 2 (and (temp ! 30) 0x3));
          n30 = or (drop_bit 2 (and (temp ! 30) 0xC)) (push_bit 2 (and (temp ! 31) 0x3));
          n31 = or (drop_bit 2 (and (temp ! 31) 0xC)) (push_bit 2 (and (temp ! 28) 0x3))
      in s1[28 := n28, 29 := n29, 30 := n30, 31 := n31])"

definition gift_128_128_extract_round_key :: "4 word list \<Rightarrow> 128 word" where
  "gift_128_128_extract_round_key key_nibbles =
     (let u = fold (\<lambda>k acc. or acc (push_bit (4 * k) (ucast (key_nibbles ! k) :: 32 word))) [0..<8] 0;
          v = fold (\<lambda>k acc. or acc (push_bit (4 * k) (ucast (key_nibbles ! (16 + k)) :: 32 word))) [0..<8] 0
      in fold (\<lambda>i acc.
                 or acc
                    (or (push_bit (4 * i + 1) (if bit u i then (1 :: 128 word) else 0))
                        (push_bit (4 * i + 2) (if bit v i then (1 :: 128 word) else 0))))
              [0..<32] 0)"

definition gift_128_128_generate_round_keys :: "128 word \<Rightarrow> 128 word list" where
  "gift_128_128_generate_round_keys master_key =
     (let key_nibbles0 = map (\<lambda>i. ucast (drop_bit (4 * i) master_key) :: 4 word) [0..<32];
          result = fold (\<lambda>_ (key_nibbles, acc).
                            (gift_128_128_update_key_state key_nibbles,
                             acc @ [gift_128_128_extract_round_key key_nibbles]))
                        [0..<gift_128_128_rounds] (key_nibbles0, [])
      in snd result)"


subsection \<open>T4: Orchestration\<close>

definition gift_128_128_round_constant_mask :: "nat \<Rightarrow> 128 word" where
  "gift_128_128_round_constant_mask round_index =
     (let rc = gift_128_128_rc ! round_index;
          top = push_bit 127 (1 :: 128 word)
      in fold (\<lambda>b acc. or acc (push_bit (4 * b + 3) (if bit rc b then (1 :: 128 word) else 0)))
              [0, 1, 2, 3, 4, 5] top)"

definition gift_128_128_encrypt_round :: "128 word \<Rightarrow> 128 word \<Rightarrow> nat \<Rightarrow> 128 word" where
  "gift_128_128_encrypt_round state round_key round_index =
     (let s1 = gift_128_128_sbox_layer state;
          s2 = gift_128_128_permutation_layer s1;
          s3 = xor s2 round_key
      in xor s3 (gift_128_128_round_constant_mask round_index))"

definition gift_128_128_decrypt_round :: "128 word \<Rightarrow> 128 word \<Rightarrow> nat \<Rightarrow> 128 word" where
  "gift_128_128_decrypt_round state round_key round_index =
     (let s1 = xor state (gift_128_128_round_constant_mask round_index);
          s2 = xor s1 round_key;
          s3 = gift_128_128_permutation_layer_inv s2
      in gift_128_128_sbox_layer_inv s3)"

function gift_128_128_encrypt_rounds_iterate ::
  "128 word \<Rightarrow> 128 word list \<Rightarrow> nat \<Rightarrow> 128 word" where
  "gift_128_128_encrypt_rounds_iterate state round_keys i =
     (if i \<ge> gift_128_128_rounds then state
      else gift_128_128_encrypt_rounds_iterate
             (gift_128_128_encrypt_round state (round_keys ! i) i) round_keys (i + 1))"
  by pat_completeness auto

termination gift_128_128_encrypt_rounds_iterate
  by (relation "measure (\<lambda>(state, round_keys, i). gift_128_128_rounds - i)")
     (auto simp: gift_128_128_rounds_def)

function gift_128_128_decrypt_rounds_iterate ::
  "128 word \<Rightarrow> 128 word list \<Rightarrow> nat \<Rightarrow> 128 word" where
  "gift_128_128_decrypt_rounds_iterate state round_keys i =
     (if i \<ge> gift_128_128_rounds then state
      else
        let round_index = gift_128_128_rounds - 1 - i
        in gift_128_128_decrypt_rounds_iterate
             (gift_128_128_decrypt_round state (round_keys ! round_index) round_index)
             round_keys (i + 1))"
  by pat_completeness auto

termination gift_128_128_decrypt_rounds_iterate
  by (relation "measure (\<lambda>(state, round_keys, i). gift_128_128_rounds - i)")
     (auto simp: gift_128_128_rounds_def)

definition gift_128_128_encrypt :: "128 word \<Rightarrow> 128 word \<Rightarrow> 128 word" where
  "gift_128_128_encrypt plaintext master_key =
     (let round_keys = gift_128_128_generate_round_keys master_key
      in gift_128_128_encrypt_rounds_iterate plaintext round_keys 0)"

definition gift_128_128_decrypt :: "128 word \<Rightarrow> 128 word \<Rightarrow> 128 word" where
  "gift_128_128_decrypt ciphertext master_key =
     (let round_keys = gift_128_128_generate_round_keys master_key
      in gift_128_128_decrypt_rounds_iterate ciphertext round_keys 0)"


subsection \<open>Test Vectors\<close>

definition gift_128_128_test_key1 :: "128 word" where
  "gift_128_128_test_key1 = 0"

definition gift_128_128_test_plaintext1 :: "128 word" where
  "gift_128_128_test_plaintext1 = 0"

definition gift_128_128_test_ciphertext1 :: "128 word" where
  "gift_128_128_test_ciphertext1 = 0xCD0BD738388AD3F668B15A36CEB6FF92"

end
