theory Xtea_64_128
  imports
    "HOL-Library.Word"
    "HOL.Bit_Operations"
begin

section \<open>XTEA 64-128: Tiered Core Definitions\<close>

subsection \<open>T1: Constants\<close>

definition xtea_64_128_block_size :: nat where
  "xtea_64_128_block_size = 64"

definition xtea_64_128_key_size :: nat where
  "xtea_64_128_key_size = 128"

definition xtea_64_128_word_size :: nat where
  "xtea_64_128_word_size = 32"

definition xtea_64_128_rounds :: nat where
  "xtea_64_128_rounds = 32"

definition xtea_64_128_delta :: "32 word" where
  "xtea_64_128_delta = 0x9E3779B9"


subsection \<open>T2: Primitives\<close>

definition xtea_64_128_round_function :: "32 word \<Rightarrow> 32 word" where
  "xtea_64_128_round_function x = xor (push_bit 4 x) (drop_bit 5 x) + x"

definition xtea_64_128_encrypt_half_round ::
  "32 word \<Rightarrow> 32 word \<Rightarrow> 32 word \<Rightarrow> 32 word \<Rightarrow> 32 word" where
  "xtea_64_128_encrypt_half_round updating source key_word sum_a =
     updating + xor (xtea_64_128_round_function source) (sum_a + key_word)"

definition xtea_64_128_decrypt_half_round ::
  "32 word \<Rightarrow> 32 word \<Rightarrow> 32 word \<Rightarrow> 32 word \<Rightarrow> 32 word" where
  "xtea_64_128_decrypt_half_round updating source key_word sum_a =
     updating - xor (xtea_64_128_round_function source) (sum_a + key_word)"


subsection \<open>T3: Structural Components\<close>

definition xtea_64_128_select_key_word :: "32 word list \<Rightarrow> 32 word \<Rightarrow> nat \<Rightarrow> 32 word" where
  "xtea_64_128_select_key_word key_words sum_a shift =
     key_words ! unat (and (drop_bit shift sum_a) 3)"


subsection \<open>T4: Orchestration\<close>

definition xtea_64_128_block_to_words :: "64 word \<Rightarrow> (32 word \<times> 32 word)" where
  "xtea_64_128_block_to_words block = (ucast (drop_bit 32 block), ucast block)"

definition xtea_64_128_words_to_block :: "32 word \<Rightarrow> 32 word \<Rightarrow> 64 word" where
  "xtea_64_128_words_to_block v0 v1 = or (push_bit 32 (ucast v0)) (ucast v1)"

definition xtea_64_128_key_to_words :: "128 word \<Rightarrow> 32 word list" where
  "xtea_64_128_key_to_words key =
     map (\<lambda>i. ucast (drop_bit (32 * (3 - i)) key) :: 32 word) [0, 1, 2, 3]"

definition xtea_64_128_encrypt_cycle ::
  "32 word \<Rightarrow> 32 word \<Rightarrow> 32 word \<Rightarrow> 32 word list \<Rightarrow> (32 word \<times> 32 word \<times> 32 word)" where
  "xtea_64_128_encrypt_cycle v0 v1 sum_a key_words =
     (let k0 = xtea_64_128_select_key_word key_words sum_a 0;
          v0a = xtea_64_128_encrypt_half_round v0 v1 k0 sum_a;
          sum_b = sum_a + xtea_64_128_delta;
          k1 = xtea_64_128_select_key_word key_words sum_b 11;
          v1a = xtea_64_128_encrypt_half_round v1 v0a k1 sum_b
      in (v0a, v1a, sum_b))"

definition xtea_64_128_decrypt_cycle ::
  "32 word \<Rightarrow> 32 word \<Rightarrow> 32 word \<Rightarrow> 32 word list \<Rightarrow> (32 word \<times> 32 word \<times> 32 word)" where
  "xtea_64_128_decrypt_cycle v0 v1 sum_a key_words =
     (let k1 = xtea_64_128_select_key_word key_words sum_a 11;
          v1a = xtea_64_128_decrypt_half_round v1 v0 k1 sum_a;
          sum_b = sum_a - xtea_64_128_delta;
          k0 = xtea_64_128_select_key_word key_words sum_b 0;
          v0a = xtea_64_128_decrypt_half_round v0 v1a k0 sum_b
      in (v0a, v1a, sum_b))"

function xtea_64_128_encrypt_rounds_iterate ::
  "32 word \<Rightarrow> 32 word \<Rightarrow> 32 word \<Rightarrow> 32 word list \<Rightarrow> nat \<Rightarrow> (32 word \<times> 32 word)" where
  "xtea_64_128_encrypt_rounds_iterate v0 v1 sum_a key_words i =
     (if i \<ge> xtea_64_128_rounds then (v0, v1)
      else
        let (v0a, v1a, sum_b) = xtea_64_128_encrypt_cycle v0 v1 sum_a key_words
        in xtea_64_128_encrypt_rounds_iterate v0a v1a sum_b key_words (i + 1))"
  by pat_completeness auto

termination xtea_64_128_encrypt_rounds_iterate
  by (relation "measure (\<lambda>(v0, v1, sum_a, key_words, i). xtea_64_128_rounds - i)")
     (auto simp: xtea_64_128_rounds_def)

function xtea_64_128_decrypt_rounds_iterate ::
  "32 word \<Rightarrow> 32 word \<Rightarrow> 32 word \<Rightarrow> 32 word list \<Rightarrow> nat \<Rightarrow> (32 word \<times> 32 word)" where
  "xtea_64_128_decrypt_rounds_iterate v0 v1 sum_a key_words i =
     (if i \<ge> xtea_64_128_rounds then (v0, v1)
      else
        let (v0a, v1a, sum_b) = xtea_64_128_decrypt_cycle v0 v1 sum_a key_words
        in xtea_64_128_decrypt_rounds_iterate v0a v1a sum_b key_words (i + 1))"
  by pat_completeness auto

termination xtea_64_128_decrypt_rounds_iterate
  by (relation "measure (\<lambda>(v0, v1, sum_a, key_words, i). xtea_64_128_rounds - i)")
     (auto simp: xtea_64_128_rounds_def)

definition xtea_64_128_encrypt :: "64 word \<Rightarrow> 128 word \<Rightarrow> 64 word" where
  "xtea_64_128_encrypt plaintext master_key =
     (let key_words = xtea_64_128_key_to_words master_key;
          (v0, v1) = xtea_64_128_block_to_words plaintext;
          (v0a, v1a) = xtea_64_128_encrypt_rounds_iterate v0 v1 0 key_words 0
      in xtea_64_128_words_to_block v0a v1a)"

definition xtea_64_128_decrypt :: "64 word \<Rightarrow> 128 word \<Rightarrow> 64 word" where
  "xtea_64_128_decrypt ciphertext master_key =
     (let key_words = xtea_64_128_key_to_words master_key;
          initial_sum = xtea_64_128_delta * of_nat xtea_64_128_rounds;
          (v0, v1) = xtea_64_128_block_to_words ciphertext;
          (v0a, v1a) = xtea_64_128_decrypt_rounds_iterate v0 v1 initial_sum key_words 0
      in xtea_64_128_words_to_block v0a v1a)"


subsection \<open>Test Vectors\<close>

definition xtea_64_128_test_key1 :: "128 word" where
  "xtea_64_128_test_key1 = 0x000102030405060708090A0B0C0D0E0F"

definition xtea_64_128_test_plaintext1 :: "64 word" where
  "xtea_64_128_test_plaintext1 = 0x4142434445464748"

definition xtea_64_128_test_ciphertext1 :: "64 word" where
  "xtea_64_128_test_ciphertext1 = 0x497DF3D072612CB5"

end
