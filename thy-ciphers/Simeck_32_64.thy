theory Simeck_32_64
  imports
    "HOL-Library.Word"
    "HOL.Bit_Operations"
begin

section \<open>SIMECK 32-64: Tiered Core Definitions\<close>

subsection \<open>T1: Constants\<close>

definition simeck_32_64_word_size :: nat where
  "simeck_32_64_word_size = 16"

definition simeck_32_64_block_size :: nat where
  "simeck_32_64_block_size = 32"

definition simeck_32_64_key_size :: nat where
  "simeck_32_64_key_size = 64"

definition simeck_32_64_rounds :: nat where
  "simeck_32_64_rounds = 32"

definition simeck_32_64_key_words :: nat where
  "simeck_32_64_key_words = 4"

definition simeck_32_64_word_mask :: "16 word" where
  "simeck_32_64_word_mask = (-1)"

definition simeck_32_64_constant :: "16 word" where
  "simeck_32_64_constant = -4"

definition simeck_32_64_sequence :: "nat list" where
  "simeck_32_64_sequence =
     [1, 1, 1, 1, 1, 0, 0, 0, 1, 1, 0, 1, 1, 1, 0, 1,
      0, 1, 0, 0, 0, 0, 1, 0, 0, 1, 0, 1, 1, 0, 0, 1]"


subsection \<open>T2: Primitives\<close>

definition simeck_32_64_rol :: "16 word \<Rightarrow> nat \<Rightarrow> 16 word" where
  "simeck_32_64_rol x r = word_rotl r x"

definition simeck_32_64_f :: "16 word \<Rightarrow> 16 word" where
  "simeck_32_64_f x = xor (and x (simeck_32_64_rol x 5)) (simeck_32_64_rol x 1)"

definition simeck_32_64_round_key_constant :: "nat \<Rightarrow> 16 word" where
  "simeck_32_64_round_key_constant round_index =
     xor simeck_32_64_constant (of_nat (simeck_32_64_sequence ! round_index))"

definition simeck_32_64_encrypt_round ::
  "16 word \<Rightarrow> (16 word \<times> 16 word) \<Rightarrow> (16 word \<times> 16 word)" where
  "simeck_32_64_encrypt_round k xy =
     (let x = fst xy;
          y = snd xy;
          fx = simeck_32_64_f x;
          new_x = xor (xor y fx) k;
          new_y = x
      in (new_x, new_y))"

definition simeck_32_64_decrypt_round ::
  "16 word \<Rightarrow> (16 word \<times> 16 word) \<Rightarrow> (16 word \<times> 16 word)" where
  "simeck_32_64_decrypt_round k xy =
     (let x = fst xy;
          y = snd xy;
          fy = simeck_32_64_f y;
          new_x = y;
          new_y = xor (xor x fy) k
      in (new_x, new_y))"


subsection \<open>T3: Structural Components (Key schedule)\<close>

definition simeck_32_64_key_to_words ::
  "64 word \<Rightarrow> (16 word \<times> 16 word \<times> 16 word \<times> 16 word)" where
  "simeck_32_64_key_to_words master_key =
     (let t0 = ucast master_key;
          t1 = ucast (drop_bit 16 master_key);
          t2 = ucast (drop_bit 32 master_key);
          t3 = ucast (drop_bit 48 master_key)
      in (t0, t1, t2, t3))"

function simeck_32_64_generate_round_keys_rec :: "16 word list \<Rightarrow> nat \<Rightarrow> 16 word list" where
  "simeck_32_64_generate_round_keys_rec states round_index =
     (if round_index \<ge> simeck_32_64_rounds then []
      else
        let round_key = states ! 0;
            k = simeck_32_64_round_key_constant round_index;
            xy = simeck_32_64_encrypt_round k (states ! 1, states ! 0);
            next_states = [states ! 1, states ! 2, states ! 3, fst xy]
        in round_key # simeck_32_64_generate_round_keys_rec next_states (round_index + 1))"
  by pat_completeness auto

termination simeck_32_64_generate_round_keys_rec
  by (relation "measure (\<lambda>(states, round_index). simeck_32_64_rounds - round_index)")
     (auto simp: simeck_32_64_rounds_def)

definition simeck_32_64_generate_round_keys :: "64 word \<Rightarrow> 16 word list" where
  "simeck_32_64_generate_round_keys master_key =
     (let (t0, t1, t2, t3) = simeck_32_64_key_to_words master_key
      in simeck_32_64_generate_round_keys_rec [t0, t1, t2, t3] 0)"


subsection \<open>T4: Orchestration\<close>

definition simeck_32_64_block_to_words :: "32 word \<Rightarrow> (16 word \<times> 16 word)" where
  "simeck_32_64_block_to_words block =
     (let left = ucast (drop_bit 16 block);
          right = ucast block
      in (left, right))"

definition simeck_32_64_words_to_block :: "16 word \<Rightarrow> 16 word \<Rightarrow> 32 word" where
  "simeck_32_64_words_to_block left right =
     or (push_bit 16 (ucast left)) (ucast right)"

function simeck_32_64_encrypt_rounds_iterate ::
  "(16 word \<times> 16 word) \<Rightarrow> 16 word list \<Rightarrow> nat \<Rightarrow> (16 word \<times> 16 word)" where
  "simeck_32_64_encrypt_rounds_iterate xy round_keys i =
     (if i \<ge> simeck_32_64_rounds then xy
      else simeck_32_64_encrypt_rounds_iterate
             (simeck_32_64_encrypt_round (round_keys ! i) xy) round_keys (i + 1))"
  by pat_completeness auto

termination simeck_32_64_encrypt_rounds_iterate
  by (relation "measure (\<lambda>(xy, round_keys, i). simeck_32_64_rounds - i)")
     (auto simp: simeck_32_64_rounds_def)

function simeck_32_64_decrypt_rounds_iterate ::
  "(16 word \<times> 16 word) \<Rightarrow> 16 word list \<Rightarrow> nat \<Rightarrow> (16 word \<times> 16 word)" where
  "simeck_32_64_decrypt_rounds_iterate xy round_keys i =
     (if i \<ge> simeck_32_64_rounds then xy
      else
        let round_index = simeck_32_64_rounds - 1 - i
        in simeck_32_64_decrypt_rounds_iterate
             (simeck_32_64_decrypt_round (round_keys ! round_index) xy) round_keys (i + 1))"
  by pat_completeness auto

termination simeck_32_64_decrypt_rounds_iterate
  by (relation "measure (\<lambda>(xy, round_keys, i). simeck_32_64_rounds - i)")
     (auto simp: simeck_32_64_rounds_def)

definition simeck_32_64_encrypt_block :: "32 word \<Rightarrow> 16 word list \<Rightarrow> 32 word" where
  "simeck_32_64_encrypt_block plaintext round_keys =
     (let xy = simeck_32_64_block_to_words plaintext;
          final_xy = simeck_32_64_encrypt_rounds_iterate xy round_keys 0
      in simeck_32_64_words_to_block (fst final_xy) (snd final_xy))"

definition simeck_32_64_decrypt_block :: "32 word \<Rightarrow> 16 word list \<Rightarrow> 32 word" where
  "simeck_32_64_decrypt_block ciphertext round_keys =
     (let xy = simeck_32_64_block_to_words ciphertext;
          final_xy = simeck_32_64_decrypt_rounds_iterate xy round_keys 0
      in simeck_32_64_words_to_block (fst final_xy) (snd final_xy))"

definition simeck_32_64_encrypt :: "32 word \<Rightarrow> 64 word \<Rightarrow> 32 word" where
  "simeck_32_64_encrypt plaintext master_key =
     (let round_keys = simeck_32_64_generate_round_keys master_key
      in simeck_32_64_encrypt_block plaintext round_keys)"

definition simeck_32_64_decrypt :: "32 word \<Rightarrow> 64 word \<Rightarrow> 32 word" where
  "simeck_32_64_decrypt ciphertext master_key =
     (let round_keys = simeck_32_64_generate_round_keys master_key
      in simeck_32_64_decrypt_block ciphertext round_keys)"


subsection \<open>Test Vectors\<close>

definition simeck_32_64_test_plaintext :: "32 word" where
  "simeck_32_64_test_plaintext = 0x65656877"

definition simeck_32_64_test_key :: "64 word" where
  "simeck_32_64_test_key = 0x1918111009080100"

definition simeck_32_64_test_ciphertext :: "32 word" where
  "simeck_32_64_test_ciphertext = 0x770D2C76"

end
