theory Gift_64_128
  imports
    "HOL-Library.Word"
    "HOL.Bit_Operations"
begin

section \<open>GIFT-64/128: Tiered Core Definitions\<close>

subsection \<open>T1: Constants\<close>

definition gift_64_128_block_size :: nat where
  "gift_64_128_block_size = 64"

definition gift_64_128_key_size :: nat where
  "gift_64_128_key_size = 128"

definition gift_64_128_rounds :: nat where
  "gift_64_128_rounds = 28"

definition gift_64_128_sbox :: "4 word list" where
  "gift_64_128_sbox = [1, 10, 4, 12, 6, 15, 3, 9, 2, 13, 11, 7, 5, 0, 8, 14]"

definition gift_64_128_pbox :: "nat list" where
  "gift_64_128_pbox =
     [0, 17, 34, 51, 48, 1, 18, 35, 32, 49, 2, 19, 16, 33, 50, 3,
      4, 21, 38, 55, 52, 5, 22, 39, 36, 53, 6, 23, 20, 37, 54, 7,
      8, 25, 42, 59, 56, 9, 26, 43, 40, 57, 10, 27, 24, 41, 58, 11,
      12, 29, 46, 63, 60, 13, 30, 47, 44, 61, 14, 31, 28, 45, 62, 15]"

definition gift_64_128_rc :: "nat list" where
  "gift_64_128_rc =
     [0x01, 0x03, 0x07, 0x0F, 0x1F, 0x3E, 0x3D, 0x3B, 0x37, 0x2F,
      0x1E, 0x3C, 0x39, 0x33, 0x27, 0x0E, 0x1D, 0x3A, 0x35, 0x2B,
      0x16, 0x2C, 0x18, 0x30, 0x21, 0x02, 0x05, 0x0B, 0x17, 0x2E,
      0x1C, 0x38, 0x31, 0x23, 0x06, 0x0D, 0x1B, 0x36, 0x2D, 0x1A,
      0x34, 0x29, 0x12, 0x24, 0x08, 0x11, 0x22, 0x04, 0x09, 0x13,
      0x26, 0x0C, 0x19, 0x32, 0x25, 0x0A, 0x15, 0x2A, 0x14, 0x28,
      0x10, 0x20]"

text \<open>Derived inverse tables (not independently specified by the cipher).\<close>

definition gift_64_128_sbox_inv :: "4 word list" where
  "gift_64_128_sbox_inv = [13, 0, 8, 6, 2, 12, 4, 11, 14, 7, 1, 10, 3, 9, 15, 5]"

definition gift_64_128_pbox_inv :: "nat list" where
  "gift_64_128_pbox_inv =
     [0, 5, 10, 15, 16, 21, 26, 31, 32, 37, 42, 47, 48, 53, 58, 63,
      12, 1, 6, 11, 28, 17, 22, 27, 44, 33, 38, 43, 60, 49, 54, 59,
      8, 13, 2, 7, 24, 29, 18, 23, 40, 45, 34, 39, 56, 61, 50, 55,
      4, 9, 14, 3, 20, 25, 30, 19, 36, 41, 46, 35, 52, 57, 62, 51]"


subsection \<open>T2: Primitives\<close>

function gift_64_128_sbox_layer_acc :: "64 word \<Rightarrow> nat \<Rightarrow> 64 word \<Rightarrow> 64 word" where
  "gift_64_128_sbox_layer_acc state i acc =
     (if i \<ge> 16 then acc
      else
        let nibble = ucast (drop_bit (4 * i) state) :: 4 word;
            sboxed = gift_64_128_sbox ! unat nibble;
            placed = push_bit (4 * i) (ucast sboxed :: 64 word)
        in gift_64_128_sbox_layer_acc state (i + 1) (or acc placed))"
  by pat_completeness auto

termination gift_64_128_sbox_layer_acc
  by (relation "measure (\<lambda>(state, i, acc). 16 - i)") auto

definition gift_64_128_sbox_layer :: "64 word \<Rightarrow> 64 word" where
  "gift_64_128_sbox_layer state = gift_64_128_sbox_layer_acc state 0 0"

function gift_64_128_sbox_layer_inv_acc :: "64 word \<Rightarrow> nat \<Rightarrow> 64 word \<Rightarrow> 64 word" where
  "gift_64_128_sbox_layer_inv_acc state i acc =
     (if i \<ge> 16 then acc
      else
        let nibble = ucast (drop_bit (4 * i) state) :: 4 word;
            sboxed = gift_64_128_sbox_inv ! unat nibble;
            placed = push_bit (4 * i) (ucast sboxed :: 64 word)
        in gift_64_128_sbox_layer_inv_acc state (i + 1) (or acc placed))"
  by pat_completeness auto

termination gift_64_128_sbox_layer_inv_acc
  by (relation "measure (\<lambda>(state, i, acc). 16 - i)") auto

definition gift_64_128_sbox_layer_inv :: "64 word \<Rightarrow> 64 word" where
  "gift_64_128_sbox_layer_inv state = gift_64_128_sbox_layer_inv_acc state 0 0"

function gift_64_128_permutation_layer_acc :: "64 word \<Rightarrow> nat \<Rightarrow> 64 word \<Rightarrow> 64 word" where
  "gift_64_128_permutation_layer_acc state i acc =
     (if i \<ge> 64 then acc
      else
        let bit_val = (if bit state i then (1 :: 64 word) else 0);
            target = gift_64_128_pbox ! i;
            placed = push_bit target bit_val
        in gift_64_128_permutation_layer_acc state (i + 1) (or acc placed))"
  by pat_completeness auto

termination gift_64_128_permutation_layer_acc
  by (relation "measure (\<lambda>(state, i, acc). 64 - i)") auto

definition gift_64_128_permutation_layer :: "64 word \<Rightarrow> 64 word" where
  "gift_64_128_permutation_layer state = gift_64_128_permutation_layer_acc state 0 0"

function gift_64_128_permutation_layer_inv_acc :: "64 word \<Rightarrow> nat \<Rightarrow> 64 word \<Rightarrow> 64 word" where
  "gift_64_128_permutation_layer_inv_acc state i acc =
     (if i \<ge> 64 then acc
      else
        let bit_val = (if bit state i then (1 :: 64 word) else 0);
            target = gift_64_128_pbox_inv ! i;
            placed = push_bit target bit_val
        in gift_64_128_permutation_layer_inv_acc state (i + 1) (or acc placed))"
  by pat_completeness auto

termination gift_64_128_permutation_layer_inv_acc
  by (relation "measure (\<lambda>(state, i, acc). 64 - i)") auto

definition gift_64_128_permutation_layer_inv :: "64 word \<Rightarrow> 64 word" where
  "gift_64_128_permutation_layer_inv state = gift_64_128_permutation_layer_inv_acc state 0 0"


subsection \<open>T3: Structural Components (Key schedule)\<close>

definition gift_64_128_update_key_state :: "4 word list \<Rightarrow> 4 word list" where
  "gift_64_128_update_key_state key_nibbles =
     (let temp = map (\<lambda>i. key_nibbles ! ((i + 8) mod 32)) [0..<32];
          s1 = temp[24 := temp ! 27, 25 := temp ! 24, 26 := temp ! 25, 27 := temp ! 26];
          n28 = or (drop_bit 2 (and (temp ! 28) 0xC)) (push_bit 2 (and (temp ! 29) 0x3));
          n29 = or (drop_bit 2 (and (temp ! 29) 0xC)) (push_bit 2 (and (temp ! 30) 0x3));
          n30 = or (drop_bit 2 (and (temp ! 30) 0xC)) (push_bit 2 (and (temp ! 31) 0x3));
          n31 = or (drop_bit 2 (and (temp ! 31) 0xC)) (push_bit 2 (and (temp ! 28) 0x3))
      in s1[28 := n28, 29 := n29, 30 := n30, 31 := n31])"

definition gift_64_128_extract_round_key :: "4 word list \<Rightarrow> 64 word" where
  "gift_64_128_extract_round_key key_nibbles =
     (let u = fold (\<lambda>k acc. or acc (push_bit (4 * k) (ucast (key_nibbles ! k) :: 16 word))) [0, 1, 2, 3] 0;
          v = fold (\<lambda>k acc. or acc (push_bit (4 * k) (ucast (key_nibbles ! (4 + k)) :: 16 word))) [0, 1, 2, 3] 0
      in fold (\<lambda>i acc.
                 or acc
                    (or (push_bit (4 * i) (if bit u i then (1 :: 64 word) else 0))
                        (push_bit (4 * i + 1) (if bit v i then (1 :: 64 word) else 0))))
              [0..<16] 0)"

definition gift_64_128_generate_round_keys :: "128 word \<Rightarrow> 64 word list" where
  "gift_64_128_generate_round_keys master_key =
     (let key_nibbles0 = map (\<lambda>i. ucast (drop_bit (4 * i) master_key) :: 4 word) [0..<32];
          result = fold (\<lambda>_ (key_nibbles, acc).
                            (gift_64_128_update_key_state key_nibbles,
                             acc @ [gift_64_128_extract_round_key key_nibbles]))
                        [0..<gift_64_128_rounds] (key_nibbles0, [])
      in snd result)"


subsection \<open>T4: Orchestration\<close>

definition gift_64_128_round_constant_mask :: "nat \<Rightarrow> 64 word" where
  "gift_64_128_round_constant_mask round_index =
     (let rc = gift_64_128_rc ! round_index;
          top = push_bit 63 (1 :: 64 word)
      in fold (\<lambda>b acc. or acc (push_bit (4 * b + 3) (if bit rc b then (1 :: 64 word) else 0)))
              [0, 1, 2, 3, 4, 5] top)"

definition gift_64_128_encrypt_round :: "64 word \<Rightarrow> 64 word \<Rightarrow> nat \<Rightarrow> 64 word" where
  "gift_64_128_encrypt_round state round_key round_index =
     (let s1 = gift_64_128_sbox_layer state;
          s2 = gift_64_128_permutation_layer s1;
          s3 = xor s2 round_key
      in xor s3 (gift_64_128_round_constant_mask round_index))"

definition gift_64_128_decrypt_round :: "64 word \<Rightarrow> 64 word \<Rightarrow> nat \<Rightarrow> 64 word" where
  "gift_64_128_decrypt_round state round_key round_index =
     (let s1 = xor state (gift_64_128_round_constant_mask round_index);
          s2 = xor s1 round_key;
          s3 = gift_64_128_permutation_layer_inv s2
      in gift_64_128_sbox_layer_inv s3)"

function gift_64_128_encrypt_rounds_iterate ::
  "64 word \<Rightarrow> 64 word list \<Rightarrow> nat \<Rightarrow> 64 word" where
  "gift_64_128_encrypt_rounds_iterate state round_keys i =
     (if i \<ge> gift_64_128_rounds then state
      else gift_64_128_encrypt_rounds_iterate
             (gift_64_128_encrypt_round state (round_keys ! i) i) round_keys (i + 1))"
  by pat_completeness auto

termination gift_64_128_encrypt_rounds_iterate
  by (relation "measure (\<lambda>(state, round_keys, i). gift_64_128_rounds - i)")
     (auto simp: gift_64_128_rounds_def)

function gift_64_128_decrypt_rounds_iterate ::
  "64 word \<Rightarrow> 64 word list \<Rightarrow> nat \<Rightarrow> 64 word" where
  "gift_64_128_decrypt_rounds_iterate state round_keys i =
     (if i \<ge> gift_64_128_rounds then state
      else
        let round_index = gift_64_128_rounds - 1 - i
        in gift_64_128_decrypt_rounds_iterate
             (gift_64_128_decrypt_round state (round_keys ! round_index) round_index)
             round_keys (i + 1))"
  by pat_completeness auto

termination gift_64_128_decrypt_rounds_iterate
  by (relation "measure (\<lambda>(state, round_keys, i). gift_64_128_rounds - i)")
     (auto simp: gift_64_128_rounds_def)

definition gift_64_128_encrypt :: "64 word \<Rightarrow> 128 word \<Rightarrow> 64 word" where
  "gift_64_128_encrypt plaintext master_key =
     (let round_keys = gift_64_128_generate_round_keys master_key
      in gift_64_128_encrypt_rounds_iterate plaintext round_keys 0)"

definition gift_64_128_decrypt :: "64 word \<Rightarrow> 128 word \<Rightarrow> 64 word" where
  "gift_64_128_decrypt ciphertext master_key =
     (let round_keys = gift_64_128_generate_round_keys master_key
      in gift_64_128_decrypt_rounds_iterate ciphertext round_keys 0)"


subsection \<open>Test Vectors\<close>

definition gift_64_128_test_key1 :: "128 word" where
  "gift_64_128_test_key1 = 0"

definition gift_64_128_test_plaintext1 :: "64 word" where
  "gift_64_128_test_plaintext1 = 0"

definition gift_64_128_test_ciphertext1 :: "64 word" where
  "gift_64_128_test_ciphertext1 = 0xF62BC3EF34F775AC"

end
