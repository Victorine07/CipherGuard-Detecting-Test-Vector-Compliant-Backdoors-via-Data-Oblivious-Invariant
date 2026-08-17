theory Cham_128_256
  imports
    "HOL-Library.Word"
    "HOL.Bit_Operations"
    "HOL.List"
begin

section \<open>CHAM-128/256: Full Core Definitions\<close>

subsection \<open>T1 Configuration Constants\<close>

definition cham_128_256_block_size :: nat where
  "cham_128_256_block_size = 128"

definition cham_128_256_key_size :: nat where
  "cham_128_256_key_size = 256"

definition cham_128_256_word_size :: nat where
  "cham_128_256_word_size = 32"

definition cham_128_256_block_words :: nat where
  "cham_128_256_block_words = 4"

definition cham_128_256_key_words :: nat where
  "cham_128_256_key_words = 8"

definition cham_128_256_round_key_words :: nat where
  "cham_128_256_round_key_words = 16"

definition cham_128_256_rounds :: nat where
  "cham_128_256_rounds = 96"

subsection \<open>T2 Primitive Operations\<close>

definition cham_128_256_rol :: "32 word \<Rightarrow> nat \<Rightarrow> 32 word" where
  "cham_128_256_rol x n = word_rotl n x"

definition cham_128_256_ror :: "32 word \<Rightarrow> nat \<Rightarrow> 32 word" where
  "cham_128_256_ror x n = word_rotr n x"

definition cham_128_256_keymix_low :: "32 word \<Rightarrow> 32 word" where
  "cham_128_256_keymix_low k =
     xor (xor k (cham_128_256_rol k 1)) (cham_128_256_rol k 8)"

definition cham_128_256_keymix_high :: "32 word \<Rightarrow> 32 word" where
  "cham_128_256_keymix_high k =
     xor (xor k (cham_128_256_rol k 1)) (cham_128_256_rol k 11)"

definition cham_128_256_encrypt_round_even ::
  "(32 word \<times> 32 word \<times> 32 word \<times> 32 word) \<Rightarrow> 32 word \<Rightarrow> nat
   \<Rightarrow> (32 word \<times> 32 word \<times> 32 word \<times> 32 word)" where
  "cham_128_256_encrypt_round_even state rk i =
     (case state of (x0, x1, x2, x3) \<Rightarrow>
        let y3 = cham_128_256_rol
                   ((xor x0 (of_nat i)) + (xor (cham_128_256_rol x1 1) rk)) 8
        in (x1, x2, x3, y3))"

definition cham_128_256_encrypt_round_odd ::
  "(32 word \<times> 32 word \<times> 32 word \<times> 32 word) \<Rightarrow> 32 word \<Rightarrow> nat
   \<Rightarrow> (32 word \<times> 32 word \<times> 32 word \<times> 32 word)" where
  "cham_128_256_encrypt_round_odd state rk i =
     (case state of (x0, x1, x2, x3) \<Rightarrow>
        let y3 = cham_128_256_rol
                   ((xor x0 (of_nat i)) + (xor (cham_128_256_rol x1 8) rk)) 1
        in (x1, x2, x3, y3))"

definition cham_128_256_decrypt_round_even ::
  "(32 word \<times> 32 word \<times> 32 word \<times> 32 word) \<Rightarrow> 32 word \<Rightarrow> nat
   \<Rightarrow> (32 word \<times> 32 word \<times> 32 word \<times> 32 word)" where
  "cham_128_256_decrypt_round_even state rk i =
     (case state of (y0, y1, y2, y3) \<Rightarrow>
        let
          x1 = y0;
          x2 = y1;
          x3 = y2;
          temp = cham_128_256_ror y3 8;
          x0 = xor (temp - (xor (cham_128_256_rol x1 1) rk)) (of_nat i)
        in
          (x0, x1, x2, x3))"

definition cham_128_256_decrypt_round_odd ::
  "(32 word \<times> 32 word \<times> 32 word \<times> 32 word) \<Rightarrow> 32 word \<Rightarrow> nat
   \<Rightarrow> (32 word \<times> 32 word \<times> 32 word \<times> 32 word)" where
  "cham_128_256_decrypt_round_odd state rk i =
     (case state of (y0, y1, y2, y3) \<Rightarrow>
        let
          x1 = y0;
          x2 = y1;
          x3 = y2;
          temp = cham_128_256_ror y3 1;
          x0 = xor (temp - (xor (cham_128_256_rol x1 8) rk)) (of_nat i)
        in
          (x0, x1, x2, x3))"

subsection \<open>T3 Key Schedule\<close>

definition cham_128_256_key_to_words :: "256 word \<Rightarrow> 32 word list" where
  "cham_128_256_key_to_words master_key = [
      ucast master_key,
      ucast (drop_bit 32 master_key),
      ucast (drop_bit 64 master_key),
      ucast (drop_bit 96 master_key),
      ucast (drop_bit 128 master_key),
      ucast (drop_bit 160 master_key),
      ucast (drop_bit 192 master_key),
      ucast (drop_bit 224 master_key)
    ]"

definition cham_128_256_init_round_keys :: "32 word list" where
  "cham_128_256_init_round_keys = replicate 16 0"

function cham_128_256_fill_round_keys ::
  "32 word list \<Rightarrow> nat \<Rightarrow> 32 word list \<Rightarrow> 32 word list" where
  "cham_128_256_fill_round_keys key_words i round_keys =
     (if i \<ge> cham_128_256_key_words then round_keys
      else
        let
          ki = key_words ! i;
          low = cham_128_256_keymix_low ki;
          high = cham_128_256_keymix_high ki;
          rk1 = round_keys[i := low];
          idx2 = xor ((i + cham_128_256_key_words) mod cham_128_256_round_key_words) 1;
          rk2 = rk1[idx2 := high]
        in
          cham_128_256_fill_round_keys key_words (i + 1) rk2)"
  by pat_completeness auto
termination
  by (relation "measure (\<lambda>(key_words, i, round_keys). cham_128_256_key_words - i)") auto

definition cham_128_256_generate_round_keys :: "32 word list \<Rightarrow> 32 word list" where
  "cham_128_256_generate_round_keys key_words =
     (if length key_words \<noteq> cham_128_256_key_words then []
      else cham_128_256_fill_round_keys key_words 0 cham_128_256_init_round_keys)"

subsection \<open>T4 Block and Key Conversions\<close>

definition cham_128_256_block_to_words ::
  "128 word \<Rightarrow> (32 word \<times> 32 word \<times> 32 word \<times> 32 word)" where
  "cham_128_256_block_to_words block =
     ( ucast block,
       ucast (drop_bit 32 block),
       ucast (drop_bit 64 block),
       ucast (drop_bit 96 block) )"

definition cham_128_256_words_to_block ::
  "32 word \<Rightarrow> 32 word \<Rightarrow> 32 word \<Rightarrow> 32 word \<Rightarrow> 128 word" where
  "cham_128_256_words_to_block x0 x1 x2 x3 =
      (ucast x0) +
      (push_bit 32 (ucast x1 :: 128 word)) +
      (push_bit 64 (ucast x2 :: 128 word)) +
      (push_bit 96 (ucast x3 :: 128 word))"

definition cham_128_256_words_to_key ::
  "32 word \<Rightarrow> 32 word \<Rightarrow> 32 word \<Rightarrow> 32 word
   \<Rightarrow> 32 word \<Rightarrow> 32 word \<Rightarrow> 32 word \<Rightarrow> 32 word
   \<Rightarrow> 256 word" where
  "cham_128_256_words_to_key k0 k1 k2 k3 k4 k5 k6 k7 =
      (ucast k0) +
      (push_bit 32  (ucast k1 :: 256 word)) +
      (push_bit 64  (ucast k2 :: 256 word)) +
      (push_bit 96  (ucast k3 :: 256 word)) +
      (push_bit 128 (ucast k4 :: 256 word)) +
      (push_bit 160 (ucast k5 :: 256 word)) +
      (push_bit 192 (ucast k6 :: 256 word)) +
      (push_bit 224 (ucast k7 :: 256 word))"

subsection \<open>T4 Encryption and Decryption Iteration\<close>

function cham_128_256_encrypt_block_iter ::
  "(32 word \<times> 32 word \<times> 32 word \<times> 32 word) \<Rightarrow> 32 word list \<Rightarrow> nat
   \<Rightarrow> (32 word \<times> 32 word \<times> 32 word \<times> 32 word)" where
  "cham_128_256_encrypt_block_iter state round_keys i =
     (if i \<ge> cham_128_256_rounds then state
      else
        let rk = round_keys ! (i mod cham_128_256_round_key_words)
        in if i mod 2 = 0 then
             cham_128_256_encrypt_block_iter
               (cham_128_256_encrypt_round_even state rk i) round_keys (i + 1)
           else
             cham_128_256_encrypt_block_iter
               (cham_128_256_encrypt_round_odd state rk i) round_keys (i + 1))"
  by pat_completeness auto
termination
  by (relation "measure (\<lambda>(state, round_keys, i). cham_128_256_rounds - i)") auto

definition cham_128_256_encrypt_block ::
  "32 word \<Rightarrow> 32 word \<Rightarrow> 32 word \<Rightarrow> 32 word \<Rightarrow> 32 word list
   \<Rightarrow> (32 word \<times> 32 word \<times> 32 word \<times> 32 word)" where
  "cham_128_256_encrypt_block x0 x1 x2 x3 round_keys =
     cham_128_256_encrypt_block_iter (x0, x1, x2, x3) round_keys 0"

function cham_128_256_decrypt_block_iter ::
  "(32 word \<times> 32 word \<times> 32 word \<times> 32 word) \<Rightarrow> 32 word list \<Rightarrow> nat
   \<Rightarrow> (32 word \<times> 32 word \<times> 32 word \<times> 32 word)" where
  "cham_128_256_decrypt_block_iter state round_keys j =
     (if j \<ge> cham_128_256_rounds then state
      else
        let
          i = cham_128_256_rounds - Suc j;
          rk = round_keys ! (i mod cham_128_256_round_key_words)
        in if i mod 2 = 0 then
             cham_128_256_decrypt_block_iter
               (cham_128_256_decrypt_round_even state rk i) round_keys (j + 1)
           else
             cham_128_256_decrypt_block_iter
               (cham_128_256_decrypt_round_odd state rk i) round_keys (j + 1))"
  by pat_completeness auto
termination
  by (relation "measure (\<lambda>(state, round_keys, j). cham_128_256_rounds - j)") auto

definition cham_128_256_decrypt_block ::
  "32 word \<Rightarrow> 32 word \<Rightarrow> 32 word \<Rightarrow> 32 word \<Rightarrow> 32 word list
   \<Rightarrow> (32 word \<times> 32 word \<times> 32 word \<times> 32 word)" where
  "cham_128_256_decrypt_block x0 x1 x2 x3 round_keys =
     cham_128_256_decrypt_block_iter (x0, x1, x2, x3) round_keys 0"

subsection \<open>T4 Top-Level Encryption and Decryption\<close>

definition cham_128_256_encrypt :: "128 word \<Rightarrow> 256 word \<Rightarrow> 128 word" where
  "cham_128_256_encrypt plaintext master_key =
     (let
        key_words = cham_128_256_key_to_words master_key;
        round_keys = cham_128_256_generate_round_keys key_words;
        state = cham_128_256_block_to_words plaintext;
        out = (case state of (x0, x1, x2, x3) \<Rightarrow>
                 cham_128_256_encrypt_block x0 x1 x2 x3 round_keys)
      in
        (case out of (y0, y1, y2, y3) \<Rightarrow>
           cham_128_256_words_to_block y0 y1 y2 y3))"

definition cham_128_256_decrypt :: "128 word \<Rightarrow> 256 word \<Rightarrow> 128 word" where
  "cham_128_256_decrypt ciphertext master_key =
     (let
        key_words = cham_128_256_key_to_words master_key;
        round_keys = cham_128_256_generate_round_keys key_words;
        state = cham_128_256_block_to_words ciphertext;
        out = (case state of (x0, x1, x2, x3) \<Rightarrow>
                 cham_128_256_decrypt_block x0 x1 x2 x3 round_keys)
      in
        (case out of (p0, p1, p2, p3) \<Rightarrow>
           cham_128_256_words_to_block p0 p1 p2 p3))"

subsection \<open>Test Vectors\<close>

definition cham_128_256_test_plaintext :: "128 word" where
  "cham_128_256_test_plaintext =
     cham_128_256_words_to_block
       0x33221100 0x77665544 0xBBAA9988 0xFFEEDDCC"

definition cham_128_256_test_key :: "256 word" where
  "cham_128_256_test_key =
     cham_128_256_words_to_key
       0x03020100 0x07060504 0x0B0A0908 0x0F0E0D0C
       0x13121110 0x17161514 0x1B1A1918 0x1F1E1D1C"

value "cham_128_256_test_plaintext"
value "cham_128_256_test_key"
value "cham_128_256_encrypt cham_128_256_test_plaintext cham_128_256_test_key"
value "cham_128_256_decrypt
         (cham_128_256_encrypt cham_128_256_test_plaintext cham_128_256_test_key)
         cham_128_256_test_key"

lemma cham_128_256_round_trip_test:
  "cham_128_256_decrypt
     (cham_128_256_encrypt cham_128_256_test_plaintext cham_128_256_test_key)
     cham_128_256_test_key
   = cham_128_256_test_plaintext"
  by eval

end