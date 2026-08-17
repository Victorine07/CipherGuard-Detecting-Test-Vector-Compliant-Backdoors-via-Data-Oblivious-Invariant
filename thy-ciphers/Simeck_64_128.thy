theory Simeck_64_128
  imports
    "HOL-Library.Word"
    "HOL.Bit_Operations"
begin

section \<open>SIMECK 64-128: Tiered Core Definitions\<close>

subsection \<open>T1: Constants\<close>

definition simeck_64_128_word_size :: nat where
  "simeck_64_128_word_size = 32"

definition simeck_64_128_block_size :: nat where
  "simeck_64_128_block_size = 64"

definition simeck_64_128_key_size :: nat where
  "simeck_64_128_key_size = 128"

definition simeck_64_128_rounds :: nat where
  "simeck_64_128_rounds = 44"

definition simeck_64_128_key_words :: nat where
  "simeck_64_128_key_words = 4"

definition simeck_64_128_word_mask :: "32 word" where
  "simeck_64_128_word_mask = (-1)"

definition simeck_64_128_constant :: "32 word" where
  "simeck_64_128_constant = -4"

definition simeck_64_128_sequence :: "nat list" where
  "simeck_64_128_sequence =
     [1, 1, 1, 1, 1, 1, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0,
      1, 1, 0, 0, 0, 1, 0, 1, 0, 0, 1, 1, 1, 1, 0, 1,
      0, 0, 0, 1, 1, 1, 0, 0, 1, 0, 0, 1, 0]"


subsection \<open>T2: Primitives\<close>

definition simeck_64_128_rol :: "32 word \<Rightarrow> nat \<Rightarrow> 32 word" where
  "simeck_64_128_rol x r = word_rotl r x"

definition simeck_64_128_f :: "32 word \<Rightarrow> 32 word" where
  "simeck_64_128_f x = xor (and x (simeck_64_128_rol x 5)) (simeck_64_128_rol x 1)"

definition simeck_64_128_round_key_constant :: "nat \<Rightarrow> 32 word" where
  "simeck_64_128_round_key_constant round_index =
     xor simeck_64_128_constant (of_nat (simeck_64_128_sequence ! round_index))"

definition simeck_64_128_encrypt_round ::
  "32 word \<Rightarrow> (32 word \<times> 32 word) \<Rightarrow> (32 word \<times> 32 word)" where
  "simeck_64_128_encrypt_round k xy =
     (let x = fst xy;
          y = snd xy;
          fx = simeck_64_128_f x;
          new_x = xor (xor y fx) k;
          new_y = x
      in (new_x, new_y))"

definition simeck_64_128_decrypt_round ::
  "32 word \<Rightarrow> (32 word \<times> 32 word) \<Rightarrow> (32 word \<times> 32 word)" where
  "simeck_64_128_decrypt_round k xy =
     (let x = fst xy;
          y = snd xy;
          fy = simeck_64_128_f y;
          new_x = y;
          new_y = xor (xor x fy) k
      in (new_x, new_y))"


subsection \<open>T3: Structural Components (Key schedule)\<close>

definition simeck_64_128_key_to_words ::
  "128 word \<Rightarrow> (32 word \<times> 32 word \<times> 32 word \<times> 32 word)" where
  "simeck_64_128_key_to_words master_key =
     (let t0 = ucast master_key;
          t1 = ucast (drop_bit 32 master_key);
          t2 = ucast (drop_bit 64 master_key);
          t3 = ucast (drop_bit 96 master_key)
      in (t0, t1, t2, t3))"

function simeck_64_128_generate_round_keys_rec :: "32 word list \<Rightarrow> nat \<Rightarrow> 32 word list" where
  "simeck_64_128_generate_round_keys_rec states round_index =
     (if round_index \<ge> simeck_64_128_rounds then []
      else
        let round_key = states ! 0;
            k = simeck_64_128_round_key_constant round_index;
            xy = simeck_64_128_encrypt_round k (states ! 1, states ! 0);
            next_states = [states ! 1, states ! 2, states ! 3, fst xy]
        in round_key # simeck_64_128_generate_round_keys_rec next_states (round_index + 1))"
  by pat_completeness auto

termination simeck_64_128_generate_round_keys_rec
  by (relation "measure (\<lambda>(states, round_index). simeck_64_128_rounds - round_index)")
     (auto simp: simeck_64_128_rounds_def)

definition simeck_64_128_generate_round_keys :: "128 word \<Rightarrow> 32 word list" where
  "simeck_64_128_generate_round_keys master_key =
     (let (t0, t1, t2, t3) = simeck_64_128_key_to_words master_key
      in simeck_64_128_generate_round_keys_rec [t0, t1, t2, t3] 0)"


subsection \<open>T4: Orchestration\<close>

definition simeck_64_128_block_to_words :: "64 word \<Rightarrow> (32 word \<times> 32 word)" where
  "simeck_64_128_block_to_words block =
     (let left = ucast (drop_bit 32 block);
          right = ucast block
      in (left, right))"

definition simeck_64_128_words_to_block :: "32 word \<Rightarrow> 32 word \<Rightarrow> 64 word" where
  "simeck_64_128_words_to_block left right =
     or (push_bit 32 (ucast left)) (ucast right)"

function simeck_64_128_encrypt_rounds_iterate ::
  "(32 word \<times> 32 word) \<Rightarrow> 32 word list \<Rightarrow> nat \<Rightarrow> (32 word \<times> 32 word)" where
  "simeck_64_128_encrypt_rounds_iterate xy round_keys i =
     (if i \<ge> simeck_64_128_rounds then xy
      else simeck_64_128_encrypt_rounds_iterate
             (simeck_64_128_encrypt_round (round_keys ! i) xy) round_keys (i + 1))"
  by pat_completeness auto

termination simeck_64_128_encrypt_rounds_iterate
  by (relation "measure (\<lambda>(xy, round_keys, i). simeck_64_128_rounds - i)")
     (auto simp: simeck_64_128_rounds_def)

function simeck_64_128_decrypt_rounds_iterate ::
  "(32 word \<times> 32 word) \<Rightarrow> 32 word list \<Rightarrow> nat \<Rightarrow> (32 word \<times> 32 word)" where
  "simeck_64_128_decrypt_rounds_iterate xy round_keys i =
     (if i \<ge> simeck_64_128_rounds then xy
      else
        let round_index = simeck_64_128_rounds - 1 - i
        in simeck_64_128_decrypt_rounds_iterate
             (simeck_64_128_decrypt_round (round_keys ! round_index) xy) round_keys (i + 1))"
  by pat_completeness auto

termination simeck_64_128_decrypt_rounds_iterate
  by (relation "measure (\<lambda>(xy, round_keys, i). simeck_64_128_rounds - i)")
     (auto simp: simeck_64_128_rounds_def)

definition simeck_64_128_encrypt_block :: "64 word \<Rightarrow> 32 word list \<Rightarrow> 64 word" where
  "simeck_64_128_encrypt_block plaintext round_keys =
     (let xy = simeck_64_128_block_to_words plaintext;
          final_xy = simeck_64_128_encrypt_rounds_iterate xy round_keys 0
      in simeck_64_128_words_to_block (fst final_xy) (snd final_xy))"

definition simeck_64_128_decrypt_block :: "64 word \<Rightarrow> 32 word list \<Rightarrow> 64 word" where
  "simeck_64_128_decrypt_block ciphertext round_keys =
     (let xy = simeck_64_128_block_to_words ciphertext;
          final_xy = simeck_64_128_decrypt_rounds_iterate xy round_keys 0
      in simeck_64_128_words_to_block (fst final_xy) (snd final_xy))"

definition simeck_64_128_encrypt :: "64 word \<Rightarrow> 128 word \<Rightarrow> 64 word" where
  "simeck_64_128_encrypt plaintext master_key =
     (let round_keys = simeck_64_128_generate_round_keys master_key
      in simeck_64_128_encrypt_block plaintext round_keys)"

definition simeck_64_128_decrypt :: "64 word \<Rightarrow> 128 word \<Rightarrow> 64 word" where
  "simeck_64_128_decrypt ciphertext master_key =
     (let round_keys = simeck_64_128_generate_round_keys master_key
      in simeck_64_128_decrypt_block ciphertext round_keys)"


subsection \<open>Test Vectors\<close>

definition simeck_64_128_test_plaintext :: "64 word" where
  "simeck_64_128_test_plaintext = 0x656B696C20646E75"

definition simeck_64_128_test_key :: "128 word" where
  "simeck_64_128_test_key = 0x1B1A1918131211100B0A090803020100"

definition simeck_64_128_test_ciphertext :: "64 word" where
  "simeck_64_128_test_ciphertext = 0x45CE69025F7AB7ED"

end
