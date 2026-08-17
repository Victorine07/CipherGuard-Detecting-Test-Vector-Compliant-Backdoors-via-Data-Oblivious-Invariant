theory Present_64_80
  imports
    "HOL-Library.Word"
    "HOL.Bit_Operations"
begin

section \<open>PRESENT 64-80: Tiered Core Definitions\<close>

subsection \<open>T1: Constants\<close>

definition present_64_80_word_size :: nat where
  "present_64_80_word_size = 4"

definition present_64_80_block_size :: nat where
  "present_64_80_block_size = 64"

definition present_64_80_key_size :: nat where
  "present_64_80_key_size = 80"

definition present_64_80_rounds :: nat where
  "present_64_80_rounds = 31"

definition present_64_80_sbox :: "4 word list" where
  "present_64_80_sbox =
     [0xC, 0x5, 0x6, 0xB, 0x9, 0x0, 0xA, 0xD, 0x3, 0xE, 0xF, 0x8, 0x4, 0x7, 0x1, 0x2]"

definition present_64_80_pbox :: "nat list" where
  "present_64_80_pbox =
     [0, 16, 32, 48, 1, 17, 33, 49, 2, 18, 34, 50, 3, 19, 35, 51,
      4, 20, 36, 52, 5, 21, 37, 53, 6, 22, 38, 54, 7, 23, 39, 55,
      8, 24, 40, 56, 9, 25, 41, 57, 10, 26, 42, 58, 11, 27, 43, 59,
      12, 28, 44, 60, 13, 29, 45, 61, 14, 30, 46, 62, 15, 31, 47, 63]"

text \<open>Derived inverse tables (not independently specified by the cipher).\<close>

definition present_64_80_sbox_inv :: "4 word list" where
  "present_64_80_sbox_inv =
     [0x5, 0xE, 0xF, 0x8, 0xC, 0x1, 0x2, 0xD, 0xB, 0x4, 0x6, 0x3, 0x0, 0x7, 0x9, 0xA]"

definition present_64_80_pbox_inv :: "nat list" where
  "present_64_80_pbox_inv =
     [0, 4, 8, 12, 16, 20, 24, 28, 32, 36, 40, 44, 48, 52, 56, 60,
      1, 5, 9, 13, 17, 21, 25, 29, 33, 37, 41, 45, 49, 53, 57, 61,
      2, 6, 10, 14, 18, 22, 26, 30, 34, 38, 42, 46, 50, 54, 58, 62,
      3, 7, 11, 15, 19, 23, 27, 31, 35, 39, 43, 47, 51, 55, 59, 63]"


subsection \<open>T2: Primitives\<close>

function present_64_80_sbox_layer_acc :: "64 word \<Rightarrow> nat \<Rightarrow> 64 word \<Rightarrow> 64 word" where
  "present_64_80_sbox_layer_acc state i acc =
     (if i \<ge> 16 then acc
      else
        let nibble = ucast (drop_bit (4 * i) state) :: 4 word;
            sboxed = present_64_80_sbox ! unat nibble;
            placed = push_bit (4 * i) (ucast sboxed :: 64 word)
        in present_64_80_sbox_layer_acc state (i + 1) (or acc placed))"
  by pat_completeness auto

termination present_64_80_sbox_layer_acc
  by (relation "measure (\<lambda>(state, i, acc). 16 - i)") auto

definition present_64_80_sbox_layer :: "64 word \<Rightarrow> 64 word" where
  "present_64_80_sbox_layer state = present_64_80_sbox_layer_acc state 0 0"

function present_64_80_sbox_layer_inv_acc :: "64 word \<Rightarrow> nat \<Rightarrow> 64 word \<Rightarrow> 64 word" where
  "present_64_80_sbox_layer_inv_acc state i acc =
     (if i \<ge> 16 then acc
      else
        let nibble = ucast (drop_bit (4 * i) state) :: 4 word;
            sboxed = present_64_80_sbox_inv ! unat nibble;
            placed = push_bit (4 * i) (ucast sboxed :: 64 word)
        in present_64_80_sbox_layer_inv_acc state (i + 1) (or acc placed))"
  by pat_completeness auto

termination present_64_80_sbox_layer_inv_acc
  by (relation "measure (\<lambda>(state, i, acc). 16 - i)") auto

definition present_64_80_sbox_layer_inv :: "64 word \<Rightarrow> 64 word" where
  "present_64_80_sbox_layer_inv state = present_64_80_sbox_layer_inv_acc state 0 0"

function present_64_80_permutation_layer_acc :: "64 word \<Rightarrow> nat \<Rightarrow> 64 word \<Rightarrow> 64 word" where
  "present_64_80_permutation_layer_acc state i acc =
     (if i \<ge> 64 then acc
      else
        let bit_val = (if bit state i then (1 :: 64 word) else 0);
            target = present_64_80_pbox ! i;
            placed = push_bit target bit_val
        in present_64_80_permutation_layer_acc state (i + 1) (or acc placed))"
  by pat_completeness auto

termination present_64_80_permutation_layer_acc
  by (relation "measure (\<lambda>(state, i, acc). 64 - i)") auto

definition present_64_80_permutation_layer :: "64 word \<Rightarrow> 64 word" where
  "present_64_80_permutation_layer state = present_64_80_permutation_layer_acc state 0 0"

function present_64_80_permutation_layer_inv_acc :: "64 word \<Rightarrow> nat \<Rightarrow> 64 word \<Rightarrow> 64 word" where
  "present_64_80_permutation_layer_inv_acc state i acc =
     (if i \<ge> 64 then acc
      else
        let bit_val = (if bit state i then (1 :: 64 word) else 0);
            target = present_64_80_pbox_inv ! i;
            placed = push_bit target bit_val
        in present_64_80_permutation_layer_inv_acc state (i + 1) (or acc placed))"
  by pat_completeness auto

termination present_64_80_permutation_layer_inv_acc
  by (relation "measure (\<lambda>(state, i, acc). 64 - i)") auto

definition present_64_80_permutation_layer_inv :: "64 word \<Rightarrow> 64 word" where
  "present_64_80_permutation_layer_inv state = present_64_80_permutation_layer_inv_acc state 0 0"


subsection \<open>T3: Structural Components (Key schedule)\<close>

definition present_64_80_update_key_register :: "80 word \<Rightarrow> nat \<Rightarrow> 80 word" where
  "present_64_80_update_key_register key round_counter =
     (let rotated = word_rotl 61 key;
          top = ucast (drop_bit 76 rotated) :: 4 word;
          sboxed_top = push_bit 76 (ucast (present_64_80_sbox ! unat top) :: 80 word);
          low_76 = and rotated (mask 76);
          after_sbox = or sboxed_top low_76;
          counter_word = push_bit 15 (of_nat round_counter :: 80 word)
      in xor after_sbox counter_word)"

definition present_64_80_extract_round_key :: "80 word \<Rightarrow> 64 word" where
  "present_64_80_extract_round_key key = ucast (drop_bit 16 key)"

function present_64_80_generate_round_keys_acc ::
  "80 word \<Rightarrow> nat \<Rightarrow> 64 word list \<Rightarrow> 64 word list" where
  "present_64_80_generate_round_keys_acc key i acc =
     (if i > present_64_80_rounds + 1 then acc
      else
        let rk = present_64_80_extract_round_key key;
            key' = present_64_80_update_key_register key i
        in present_64_80_generate_round_keys_acc key' (i + 1) (acc @ [rk]))"
  by pat_completeness auto

termination present_64_80_generate_round_keys_acc
  by (relation "measure (\<lambda>(key, i, acc). (present_64_80_rounds + 2) - i)")
     (auto simp: present_64_80_rounds_def)

definition present_64_80_generate_round_keys :: "80 word \<Rightarrow> 64 word list" where
  "present_64_80_generate_round_keys master_key =
     present_64_80_generate_round_keys_acc master_key 1 []"


subsection \<open>T4: Orchestration\<close>

definition present_64_80_encrypt_round :: "64 word \<Rightarrow> 64 word \<Rightarrow> 64 word" where
  "present_64_80_encrypt_round state round_key =
     present_64_80_permutation_layer (present_64_80_sbox_layer (xor state round_key))"

definition present_64_80_decrypt_round :: "64 word \<Rightarrow> 64 word \<Rightarrow> 64 word" where
  "present_64_80_decrypt_round state round_key =
     present_64_80_sbox_layer_inv (present_64_80_permutation_layer_inv (xor state round_key))"

function present_64_80_encrypt_rounds_iterate ::
  "64 word \<Rightarrow> 64 word list \<Rightarrow> nat \<Rightarrow> 64 word" where
  "present_64_80_encrypt_rounds_iterate state round_keys i =
     (if i \<ge> present_64_80_rounds then xor state (round_keys ! present_64_80_rounds)
      else present_64_80_encrypt_rounds_iterate
             (present_64_80_encrypt_round state (round_keys ! i)) round_keys (i + 1))"
  by pat_completeness auto

termination present_64_80_encrypt_rounds_iterate
  by (relation "measure (\<lambda>(state, round_keys, i). present_64_80_rounds - i)")
     (auto simp: present_64_80_rounds_def)

function present_64_80_decrypt_rounds_iterate ::
  "64 word \<Rightarrow> 64 word list \<Rightarrow> nat \<Rightarrow> 64 word" where
  "present_64_80_decrypt_rounds_iterate state round_keys i =
     (if i \<ge> present_64_80_rounds then xor state (round_keys ! 0)
      else present_64_80_decrypt_rounds_iterate
             (present_64_80_decrypt_round state (round_keys ! (present_64_80_rounds - i)))
             round_keys (i + 1))"
  by pat_completeness auto

termination present_64_80_decrypt_rounds_iterate
  by (relation "measure (\<lambda>(state, round_keys, i). present_64_80_rounds - i)")
     (auto simp: present_64_80_rounds_def)

definition present_64_80_encrypt :: "64 word \<Rightarrow> 80 word \<Rightarrow> 64 word" where
  "present_64_80_encrypt plaintext master_key =
     (let round_keys = present_64_80_generate_round_keys master_key
      in present_64_80_encrypt_rounds_iterate plaintext round_keys 0)"

definition present_64_80_decrypt :: "64 word \<Rightarrow> 80 word \<Rightarrow> 64 word" where
  "present_64_80_decrypt ciphertext master_key =
     (let round_keys = present_64_80_generate_round_keys master_key
      in present_64_80_decrypt_rounds_iterate ciphertext round_keys 0)"


subsection \<open>Test Vectors\<close>

definition present_64_80_test_key1 :: "80 word" where
  "present_64_80_test_key1 = 0"

definition present_64_80_test_plaintext1 :: "64 word" where
  "present_64_80_test_plaintext1 = 0"

definition present_64_80_test_ciphertext1 :: "64 word" where
  "present_64_80_test_ciphertext1 = 0x5579C1387B228445"

definition present_64_80_test_key2 :: "80 word" where
  "present_64_80_test_key2 = 0xFFFFFFFFFFFFFFFFFFFF"

definition present_64_80_test_plaintext2 :: "64 word" where
  "present_64_80_test_plaintext2 = 0xFFFFFFFFFFFFFFFF"

definition present_64_80_test_ciphertext2 :: "64 word" where
  "present_64_80_test_ciphertext2 = 0x3333DCD3213210D2"

end
