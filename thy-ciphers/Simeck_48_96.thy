theory Simeck_48_96
  imports
    "HOL-Library.Word"
    "HOL.Bit_Operations"
begin

section \<open>SIMECK 48-96: Tiered Core Definitions\<close>

subsection \<open>T1: Constants\<close>

definition simeck_48_96_word_size :: nat where
  "simeck_48_96_word_size = 24"

definition simeck_48_96_block_size :: nat where
  "simeck_48_96_block_size = 48"

definition simeck_48_96_key_size :: nat where
  "simeck_48_96_key_size = 96"

definition simeck_48_96_rounds :: nat where
  "simeck_48_96_rounds = 36"

definition simeck_48_96_key_words :: nat where
  "simeck_48_96_key_words = 4"

definition simeck_48_96_word_mask :: "24 word" where
  "simeck_48_96_word_mask = (-1)"

definition simeck_48_96_constant :: "24 word" where
  "simeck_48_96_constant = -4"

definition simeck_48_96_sequence :: "nat list" where
  "simeck_48_96_sequence =
     [1, 1, 1, 1, 1, 0, 0, 0, 1, 1, 0, 1, 1, 1, 0, 1,
      0, 1, 0, 0, 0, 0, 1, 0, 0, 1, 0, 1, 1, 0, 0, 1,
      1, 1, 1, 1]"


subsection \<open>T2: Primitives\<close>

definition simeck_48_96_rol :: "24 word \<Rightarrow> nat \<Rightarrow> 24 word" where
  "simeck_48_96_rol x r = word_rotl r x"

definition simeck_48_96_f :: "24 word \<Rightarrow> 24 word" where
  "simeck_48_96_f x = xor (and x (simeck_48_96_rol x 5)) (simeck_48_96_rol x 1)"

definition simeck_48_96_round_key_constant :: "nat \<Rightarrow> 24 word" where
  "simeck_48_96_round_key_constant round_index =
     xor simeck_48_96_constant (of_nat (simeck_48_96_sequence ! round_index))"

definition simeck_48_96_encrypt_round ::
  "24 word \<Rightarrow> (24 word \<times> 24 word) \<Rightarrow> (24 word \<times> 24 word)" where
  "simeck_48_96_encrypt_round k xy =
     (let x = fst xy;
          y = snd xy;
          fx = simeck_48_96_f x;
          new_x = xor (xor y fx) k;
          new_y = x
      in (new_x, new_y))"

definition simeck_48_96_decrypt_round ::
  "24 word \<Rightarrow> (24 word \<times> 24 word) \<Rightarrow> (24 word \<times> 24 word)" where
  "simeck_48_96_decrypt_round k xy =
     (let x = fst xy;
          y = snd xy;
          fy = simeck_48_96_f y;
          new_x = y;
          new_y = xor (xor x fy) k
      in (new_x, new_y))"


subsection \<open>T3: Structural Components (Key schedule)\<close>

definition simeck_48_96_key_to_words ::
  "96 word \<Rightarrow> (24 word \<times> 24 word \<times> 24 word \<times> 24 word)" where
  "simeck_48_96_key_to_words master_key =
     (let t0 = ucast master_key;
          t1 = ucast (drop_bit 24 master_key);
          t2 = ucast (drop_bit 48 master_key);
          t3 = ucast (drop_bit 72 master_key)
      in (t0, t1, t2, t3))"

function simeck_48_96_generate_round_keys_rec :: "24 word list \<Rightarrow> nat \<Rightarrow> 24 word list" where
  "simeck_48_96_generate_round_keys_rec states round_index =
     (if round_index \<ge> simeck_48_96_rounds then []
      else
        let round_key = states ! 0;
            k = simeck_48_96_round_key_constant round_index;
            xy = simeck_48_96_encrypt_round k (states ! 1, states ! 0);
            next_states = [states ! 1, states ! 2, states ! 3, fst xy]
        in round_key # simeck_48_96_generate_round_keys_rec next_states (round_index + 1))"
  by pat_completeness auto

termination simeck_48_96_generate_round_keys_rec
  by (relation "measure (\<lambda>(states, round_index). simeck_48_96_rounds - round_index)")
     (auto simp: simeck_48_96_rounds_def)

definition simeck_48_96_generate_round_keys :: "96 word \<Rightarrow> 24 word list" where
  "simeck_48_96_generate_round_keys master_key =
     (let (t0, t1, t2, t3) = simeck_48_96_key_to_words master_key
      in simeck_48_96_generate_round_keys_rec [t0, t1, t2, t3] 0)"


subsection \<open>T4: Orchestration\<close>

definition simeck_48_96_block_to_words :: "48 word \<Rightarrow> (24 word \<times> 24 word)" where
  "simeck_48_96_block_to_words block =
     (let left = ucast (drop_bit 24 block);
          right = ucast block
      in (left, right))"

definition simeck_48_96_words_to_block :: "24 word \<Rightarrow> 24 word \<Rightarrow> 48 word" where
  "simeck_48_96_words_to_block left right =
     or (push_bit 24 (ucast left)) (ucast right)"

function simeck_48_96_encrypt_rounds_iterate ::
  "(24 word \<times> 24 word) \<Rightarrow> 24 word list \<Rightarrow> nat \<Rightarrow> (24 word \<times> 24 word)" where
  "simeck_48_96_encrypt_rounds_iterate xy round_keys i =
     (if i \<ge> simeck_48_96_rounds then xy
      else simeck_48_96_encrypt_rounds_iterate
             (simeck_48_96_encrypt_round (round_keys ! i) xy) round_keys (i + 1))"
  by pat_completeness auto

termination simeck_48_96_encrypt_rounds_iterate
  by (relation "measure (\<lambda>(xy, round_keys, i). simeck_48_96_rounds - i)")
     (auto simp: simeck_48_96_rounds_def)

function simeck_48_96_decrypt_rounds_iterate ::
  "(24 word \<times> 24 word) \<Rightarrow> 24 word list \<Rightarrow> nat \<Rightarrow> (24 word \<times> 24 word)" where
  "simeck_48_96_decrypt_rounds_iterate xy round_keys i =
     (if i \<ge> simeck_48_96_rounds then xy
      else
        let round_index = simeck_48_96_rounds - 1 - i
        in simeck_48_96_decrypt_rounds_iterate
             (simeck_48_96_decrypt_round (round_keys ! round_index) xy) round_keys (i + 1))"
  by pat_completeness auto

termination simeck_48_96_decrypt_rounds_iterate
  by (relation "measure (\<lambda>(xy, round_keys, i). simeck_48_96_rounds - i)")
     (auto simp: simeck_48_96_rounds_def)

definition simeck_48_96_encrypt_block :: "48 word \<Rightarrow> 24 word list \<Rightarrow> 48 word" where
  "simeck_48_96_encrypt_block plaintext round_keys =
     (let xy = simeck_48_96_block_to_words plaintext;
          final_xy = simeck_48_96_encrypt_rounds_iterate xy round_keys 0
      in simeck_48_96_words_to_block (fst final_xy) (snd final_xy))"

definition simeck_48_96_decrypt_block :: "48 word \<Rightarrow> 24 word list \<Rightarrow> 48 word" where
  "simeck_48_96_decrypt_block ciphertext round_keys =
     (let xy = simeck_48_96_block_to_words ciphertext;
          final_xy = simeck_48_96_decrypt_rounds_iterate xy round_keys 0
      in simeck_48_96_words_to_block (fst final_xy) (snd final_xy))"

definition simeck_48_96_encrypt :: "48 word \<Rightarrow> 96 word \<Rightarrow> 48 word" where
  "simeck_48_96_encrypt plaintext master_key =
     (let round_keys = simeck_48_96_generate_round_keys master_key
      in simeck_48_96_encrypt_block plaintext round_keys)"

definition simeck_48_96_decrypt :: "48 word \<Rightarrow> 96 word \<Rightarrow> 48 word" where
  "simeck_48_96_decrypt ciphertext master_key =
     (let round_keys = simeck_48_96_generate_round_keys master_key
      in simeck_48_96_decrypt_block ciphertext round_keys)"


subsection \<open>Test Vectors\<close>

definition simeck_48_96_test_plaintext :: "48 word" where
  "simeck_48_96_test_plaintext = 0x72696320646E"

definition simeck_48_96_test_key :: "96 word" where
  "simeck_48_96_test_key = 0x1A19181211100A0908020100"

definition simeck_48_96_test_ciphertext :: "48 word" where
  "simeck_48_96_test_ciphertext = 0xF3CF25E33B36"

end
