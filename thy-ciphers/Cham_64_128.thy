theory Cham_64_128
  imports
    "HOL-Library.Word"
    "HOL.Bit_Operations"
    "HOL.List"
begin

section \<open>CHAM-64/128: Full Core Definitions\<close>

subsection \<open>T1 Configuration Constants\<close>

definition cham_64_128_block_size :: nat where
  "cham_64_128_block_size = 64"

definition cham_64_128_key_size :: nat where
  "cham_64_128_key_size = 128"

definition cham_64_128_word_size :: nat where
  "cham_64_128_word_size = 16"

definition cham_64_128_block_words :: nat where
  "cham_64_128_block_words = 4"

definition cham_64_128_key_words :: nat where
  "cham_64_128_key_words = 8"

definition cham_64_128_round_key_words :: nat where
  "cham_64_128_round_key_words = 16"

definition cham_64_128_rounds :: nat where
  "cham_64_128_rounds = 80"

subsection \<open>T2 Primitive Operations\<close>

definition cham_64_128_rol :: "16 word \<Rightarrow> nat \<Rightarrow> 16 word" where
  "cham_64_128_rol x n = word_rotl n x"

definition cham_64_128_ror :: "16 word \<Rightarrow> nat \<Rightarrow> 16 word" where
  "cham_64_128_ror x n = word_rotr n x"

definition cham_64_128_keymix_low :: "16 word \<Rightarrow> 16 word" where
  "cham_64_128_keymix_low k =
     xor (xor k (cham_64_128_rol k 1)) (cham_64_128_rol k 8)"

definition cham_64_128_keymix_high :: "16 word \<Rightarrow> 16 word" where
  "cham_64_128_keymix_high k =
     xor (xor k (cham_64_128_rol k 1)) (cham_64_128_rol k 11)"

definition cham_64_128_encrypt_round_even ::
  "(16 word \<times> 16 word \<times> 16 word \<times> 16 word) \<Rightarrow> 16 word \<Rightarrow> nat
   \<Rightarrow> (16 word \<times> 16 word \<times> 16 word \<times> 16 word)" where
  "cham_64_128_encrypt_round_even state rk i =
     (case state of (x0, x1, x2, x3) \<Rightarrow>
        let y3 = cham_64_128_rol
                   ((xor x0 (of_nat i)) + (xor (cham_64_128_rol x1 1) rk)) 8
        in (x1, x2, x3, y3))"

definition cham_64_128_encrypt_round_odd ::
  "(16 word \<times> 16 word \<times> 16 word \<times> 16 word) \<Rightarrow> 16 word \<Rightarrow> nat
   \<Rightarrow> (16 word \<times> 16 word \<times> 16 word \<times> 16 word)" where
  "cham_64_128_encrypt_round_odd state rk i =
     (case state of (x0, x1, x2, x3) \<Rightarrow>
        let y3 = cham_64_128_rol
                   ((xor x0 (of_nat i)) + (xor (cham_64_128_rol x1 8) rk)) 1
        in (x1, x2, x3, y3))"

definition cham_64_128_decrypt_round_even ::
  "(16 word \<times> 16 word \<times> 16 word \<times> 16 word) \<Rightarrow> 16 word \<Rightarrow> nat
   \<Rightarrow> (16 word \<times> 16 word \<times> 16 word \<times> 16 word)" where
  "cham_64_128_decrypt_round_even state rk i =
     (case state of (y0, y1, y2, y3) \<Rightarrow>
        let
          x1 = y0;
          x2 = y1;
          x3 = y2;
          temp = cham_64_128_ror y3 8;
          x0 = xor (temp - (xor (cham_64_128_rol x1 1) rk)) (of_nat i)
        in
          (x0, x1, x2, x3))"

definition cham_64_128_decrypt_round_odd ::
  "(16 word \<times> 16 word \<times> 16 word \<times> 16 word) \<Rightarrow> 16 word \<Rightarrow> nat
   \<Rightarrow> (16 word \<times> 16 word \<times> 16 word \<times> 16 word)" where
  "cham_64_128_decrypt_round_odd state rk i =
     (case state of (y0, y1, y2, y3) \<Rightarrow>
        let
          x1 = y0;
          x2 = y1;
          x3 = y2;
          temp = cham_64_128_ror y3 1;
          x0 = xor (temp - (xor (cham_64_128_rol x1 8) rk)) (of_nat i)
        in
          (x0, x1, x2, x3))"

subsection \<open>T3 Key Schedule\<close>

definition cham_64_128_key_to_words :: "128 word \<Rightarrow> 16 word list" where
  "cham_64_128_key_to_words master_key = [
      ucast master_key,
      ucast (drop_bit 16 master_key),
      ucast (drop_bit 32 master_key),
      ucast (drop_bit 48 master_key),
      ucast (drop_bit 64 master_key),
      ucast (drop_bit 80 master_key),
      ucast (drop_bit 96 master_key),
      ucast (drop_bit 112 master_key)
    ]"

definition cham_64_128_init_round_keys :: "16 word list" where
  "cham_64_128_init_round_keys = replicate 16 0"

function cham_64_128_fill_round_keys ::
  "16 word list \<Rightarrow> nat \<Rightarrow> 16 word list \<Rightarrow> 16 word list" where
  "cham_64_128_fill_round_keys key_words i round_keys =
     (if i \<ge> cham_64_128_key_words then round_keys
      else
        let
          ki = key_words ! i;
          low = cham_64_128_keymix_low ki;
          high = cham_64_128_keymix_high ki;
          rk1 = round_keys[i := low];
          idx2 = xor ((i + cham_64_128_key_words) mod cham_64_128_round_key_words) 1;
          rk2 = rk1[idx2 := high]
        in
          cham_64_128_fill_round_keys key_words (i + 1) rk2)"
  by pat_completeness auto
termination
  by (relation "measure (\<lambda>(key_words, i, round_keys). cham_64_128_key_words - i)") auto

definition cham_64_128_generate_round_keys :: "16 word list \<Rightarrow> 16 word list" where
  "cham_64_128_generate_round_keys key_words =
     (if length key_words \<noteq> cham_64_128_key_words then []
      else cham_64_128_fill_round_keys key_words 0 cham_64_128_init_round_keys)"

subsection \<open>T4 Block Conversions\<close>

definition cham_64_128_block_to_words ::
  "64 word \<Rightarrow> (16 word \<times> 16 word \<times> 16 word \<times> 16 word)" where
  "cham_64_128_block_to_words block =
     ( ucast block,
       ucast (drop_bit 16 block),
       ucast (drop_bit 32 block),
       ucast (drop_bit 48 block) )"

definition cham_64_128_words_to_block ::
  "16 word \<Rightarrow> 16 word \<Rightarrow> 16 word \<Rightarrow> 16 word \<Rightarrow> 64 word" where
  "cham_64_128_words_to_block x0 x1 x2 x3 =
      or (ucast x0)
        (or (push_bit 16 (ucast x1))
          (or (push_bit 32 (ucast x2))
              (push_bit 48 (ucast x3))))"

subsection \<open>T4 Encryption and Decryption Iteration\<close>

function cham_64_128_encrypt_block_iter ::
  "(16 word \<times> 16 word \<times> 16 word \<times> 16 word) \<Rightarrow> 16 word list \<Rightarrow> nat
   \<Rightarrow> (16 word \<times> 16 word \<times> 16 word \<times> 16 word)" where
  "cham_64_128_encrypt_block_iter state round_keys i =
     (if i \<ge> cham_64_128_rounds then state
      else
        let rk = round_keys ! (i mod cham_64_128_round_key_words)
        in if i mod 2 = 0 then
             cham_64_128_encrypt_block_iter
               (cham_64_128_encrypt_round_even state rk i) round_keys (i + 1)
           else
             cham_64_128_encrypt_block_iter
               (cham_64_128_encrypt_round_odd state rk i) round_keys (i + 1))"
  by pat_completeness auto
termination
  by (relation "measure (\<lambda>(state, round_keys, i). cham_64_128_rounds - i)") auto

definition cham_64_128_encrypt_block ::
  "16 word \<Rightarrow> 16 word \<Rightarrow> 16 word \<Rightarrow> 16 word \<Rightarrow> 16 word list
   \<Rightarrow> (16 word \<times> 16 word \<times> 16 word \<times> 16 word)" where
  "cham_64_128_encrypt_block x0 x1 x2 x3 round_keys =
     cham_64_128_encrypt_block_iter (x0, x1, x2, x3) round_keys 0"

function cham_64_128_decrypt_block_iter ::
  "(16 word \<times> 16 word \<times> 16 word \<times> 16 word) \<Rightarrow> 16 word list \<Rightarrow> nat
   \<Rightarrow> (16 word \<times> 16 word \<times> 16 word \<times> 16 word)" where
  "cham_64_128_decrypt_block_iter state round_keys j =
     (if j \<ge> cham_64_128_rounds then state
      else
        let
          i = cham_64_128_rounds - Suc j;
          rk = round_keys ! (i mod cham_64_128_round_key_words)
        in if i mod 2 = 0 then
             cham_64_128_decrypt_block_iter
               (cham_64_128_decrypt_round_even state rk i) round_keys (j + 1)
           else
             cham_64_128_decrypt_block_iter
               (cham_64_128_decrypt_round_odd state rk i) round_keys (j + 1))"
  by pat_completeness auto
termination
  by (relation "measure (\<lambda>(state, round_keys, j). cham_64_128_rounds - j)") auto

definition cham_64_128_decrypt_block ::
  "16 word \<Rightarrow> 16 word \<Rightarrow> 16 word \<Rightarrow> 16 word \<Rightarrow> 16 word list
   \<Rightarrow> (16 word \<times> 16 word \<times> 16 word \<times> 16 word)" where
  "cham_64_128_decrypt_block x0 x1 x2 x3 round_keys =
     cham_64_128_decrypt_block_iter (x0, x1, x2, x3) round_keys 0"

subsection \<open>T4 Top-Level Encryption and Decryption\<close>

definition cham_64_128_encrypt :: "64 word \<Rightarrow> 128 word \<Rightarrow> 64 word" where
  "cham_64_128_encrypt plaintext master_key =
     (let
        key_words = cham_64_128_key_to_words master_key;
        round_keys = cham_64_128_generate_round_keys key_words;
        state = cham_64_128_block_to_words plaintext;
        out = (case state of (x0, x1, x2, x3) \<Rightarrow>
                 cham_64_128_encrypt_block x0 x1 x2 x3 round_keys)
      in
        (case out of (y0, y1, y2, y3) \<Rightarrow>
           cham_64_128_words_to_block y0 y1 y2 y3))"

definition cham_64_128_decrypt :: "64 word \<Rightarrow> 128 word \<Rightarrow> 64 word" where
  "cham_64_128_decrypt ciphertext master_key =
     (let
        key_words = cham_64_128_key_to_words master_key;
        round_keys = cham_64_128_generate_round_keys key_words;
        state = cham_64_128_block_to_words ciphertext;
        out = (case state of (x0, x1, x2, x3) \<Rightarrow>
                 cham_64_128_decrypt_block x0 x1 x2 x3 round_keys)
      in
        (case out of (p0, p1, p2, p3) \<Rightarrow>
           cham_64_128_words_to_block p0 p1 p2 p3))"

subsection \<open>Test Vectors\<close>

definition cham_64_128_test_plaintext :: "64 word" where
  "cham_64_128_test_plaintext =
     cham_64_128_words_to_block 0x1100 0x3322 0x5544 0x7766"

definition cham_64_128_words_to_key ::
  "16 word \<Rightarrow> 16 word \<Rightarrow> 16 word \<Rightarrow> 16 word
   \<Rightarrow> 16 word \<Rightarrow> 16 word \<Rightarrow> 16 word \<Rightarrow> 16 word
   \<Rightarrow> 128 word" where
  "cham_64_128_words_to_key k0 k1 k2 k3 k4 k5 k6 k7 =
     (ucast k0) +
     (push_bit 16  (ucast k1 :: 128 word)) +
     (push_bit 32  (ucast k2 :: 128 word)) +
     (push_bit 48  (ucast k3 :: 128 word)) +
     (push_bit 64  (ucast k4 :: 128 word)) +
     (push_bit 80  (ucast k5 :: 128 word)) +
     (push_bit 96  (ucast k6 :: 128 word)) +
     (push_bit 112 (ucast k7 :: 128 word))"

definition cham_64_128_test_key :: "128 word" where
  "cham_64_128_test_key =
     cham_64_128_words_to_key
       0x0100 0x0302 0x0504 0x0706
       0x0908 0x0B0A 0x0D0C 0x0F0E"


definition cham_64_128_test_expected_ciphertext :: "64 word" where
  "cham_64_128_test_expected_ciphertext =
     cham_64_128_words_to_block 0x453C 0x63BC 0xDCFA 0xBF4E"

value "cham_64_128_test_plaintext"
value "cham_64_128_test_key"
value "cham_64_128_test_expected_ciphertext"

value "cham_64_128_encrypt cham_64_128_test_plaintext cham_64_128_test_key"
value "cham_64_128_decrypt cham_64_128_test_expected_ciphertext cham_64_128_test_key"

lemma cham_64_128_encrypt_test_vector:
  "cham_64_128_encrypt cham_64_128_test_plaintext cham_64_128_test_key =
   cham_64_128_test_expected_ciphertext"
  by eval

lemma cham_64_128_decrypt_test_vector:
  "cham_64_128_decrypt cham_64_128_test_expected_ciphertext cham_64_128_test_key =
   cham_64_128_test_plaintext"
  by eval

lemma cham_64_128_round_trip_test:
  "cham_64_128_decrypt
     (cham_64_128_encrypt cham_64_128_test_plaintext cham_64_128_test_key)
     cham_64_128_test_key
   = cham_64_128_test_plaintext"
  by eval

end