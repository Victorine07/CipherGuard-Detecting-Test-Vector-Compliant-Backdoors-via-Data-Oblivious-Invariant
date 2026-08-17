theory Skinny_64_192
  imports
    "HOL-Library.Word"
    "HOL.Bit_Operations"
begin

section \<open>SKINNY 64-192 (TK3): Tiered Core Definitions\<close>

subsection \<open>T1: Constants\<close>

definition skinny_64_192_block_size :: nat where
  "skinny_64_192_block_size = 64"

definition skinny_64_192_key_size :: nat where
  "skinny_64_192_key_size = 192"

definition skinny_64_192_rounds :: nat where
  "skinny_64_192_rounds = 40"

definition skinny_64_192_tweakey_blocks :: nat where
  "skinny_64_192_tweakey_blocks = 3"

definition skinny_64_192_sbox :: "4 word list" where
  "skinny_64_192_sbox = [12, 6, 9, 0, 1, 10, 2, 11, 3, 8, 5, 13, 4, 14, 7, 15]"

definition skinny_64_192_rc :: "nat list" where
  "skinny_64_192_rc =
     [0x01, 0x03, 0x07, 0x0F, 0x1F, 0x3E, 0x3D, 0x3B, 0x37, 0x2F,
      0x1E, 0x3C, 0x39, 0x33, 0x27, 0x0E, 0x1D, 0x3A, 0x35, 0x2B,
      0x16, 0x2C, 0x18, 0x30, 0x21, 0x02, 0x05, 0x0B, 0x17, 0x2E,
      0x1C, 0x38, 0x31, 0x23, 0x06, 0x0D, 0x1B, 0x36, 0x2D, 0x1A,
      0x34, 0x29, 0x12, 0x24, 0x08, 0x11, 0x22, 0x04, 0x09, 0x13,
      0x26, 0x0C, 0x19, 0x32, 0x25, 0x0A, 0x15, 0x2A, 0x14, 0x28,
      0x10, 0x20]"

text \<open>Derived inverse table (not independently specified by the cipher).\<close>

definition skinny_64_192_sbox_inv :: "4 word list" where
  "skinny_64_192_sbox_inv = [3, 4, 6, 8, 12, 10, 1, 14, 9, 2, 5, 7, 0, 11, 13, 15]"


subsection \<open>T2: Primitives\<close>

definition skinny_64_192_sub_cells :: "4 word list \<Rightarrow> 4 word list" where
  "skinny_64_192_sub_cells state = map (\<lambda>c. skinny_64_192_sbox ! unat c) state"

definition skinny_64_192_sub_cells_inv :: "4 word list \<Rightarrow> 4 word list" where
  "skinny_64_192_sub_cells_inv state = map (\<lambda>c. skinny_64_192_sbox_inv ! unat c) state"

definition skinny_64_192_shift_rows :: "4 word list \<Rightarrow> 4 word list" where
  "skinny_64_192_shift_rows state =
     map (\<lambda>i. state ! i) [0, 1, 2, 3, 7, 4, 5, 6, 10, 11, 8, 9, 13, 14, 15, 12]"

definition skinny_64_192_shift_rows_inv :: "4 word list \<Rightarrow> 4 word list" where
  "skinny_64_192_shift_rows_inv state =
     map (\<lambda>i. state ! i) [0, 1, 2, 3, 5, 6, 7, 4, 10, 11, 8, 9, 15, 12, 13, 14]"

definition skinny_64_192_mix_columns :: "4 word list \<Rightarrow> 4 word list" where
  "skinny_64_192_mix_columns state =
     (let r0 = take 4 state;
          r1 = take 4 (drop 4 state);
          r2 = take 4 (drop 8 state);
          r3 = take 4 (drop 12 state);
          r0_xor_r2 = map (\<lambda>p. xor (fst p) (snd p)) (zip r0 r2);
          new_r0 = map (\<lambda>p. xor (fst p) (snd p)) (zip r0_xor_r2 r3);
          new_r2 = map (\<lambda>p. xor (fst p) (snd p)) (zip r1 r2)
      in new_r0 @ r0 @ new_r2 @ r0_xor_r2)"

definition skinny_64_192_mix_columns_inv :: "4 word list \<Rightarrow> 4 word list" where
  "skinny_64_192_mix_columns_inv state =
     (let r0 = take 4 state;
          r1 = take 4 (drop 4 state);
          r2 = take 4 (drop 8 state);
          r3 = take 4 (drop 12 state);
          new_r2 = map (\<lambda>p. xor (fst p) (snd p)) (zip r1 r3);
          new_r1 = map (\<lambda>p. xor (fst p) (snd p)) (zip r2 new_r2);
          new_r3 = map (\<lambda>p. xor (fst p) (snd p)) (zip r0 r3)
      in r1 @ new_r1 @ new_r2 @ new_r3)"


subsection \<open>T3: Structural Components (Tweakey schedule)\<close>

definition skinny_64_192_block_to_state :: "64 word \<Rightarrow> 4 word list" where
  "skinny_64_192_block_to_state block =
     map (\<lambda>i. ucast (drop_bit (64 - 4 * (i + 1)) block) :: 4 word) [0..<16]"

definition skinny_64_192_state_to_block :: "4 word list \<Rightarrow> 64 word" where
  "skinny_64_192_state_to_block state = foldl (\<lambda>acc c. or (push_bit 4 acc) (ucast c)) (0 :: 64 word) state"

definition skinny_64_192_key_to_tweakey_state :: "192 word \<Rightarrow> 4 word list list" where
  "skinny_64_192_key_to_tweakey_state master_key =
     map (\<lambda>z. skinny_64_192_block_to_state (ucast (drop_bit (64 * (2 - z)) master_key) :: 64 word)) [0, 1, 2]"

definition skinny_64_192_apply_pt :: "4 word list \<Rightarrow> 4 word list" where
  "skinny_64_192_apply_pt twky =
     (let row2 = take 4 (drop 8 twky); row3 = take 4 (drop 12 twky)
      in [row2 ! 1, row3 ! 3, row2 ! 0, row3 ! 1] @ [row2 ! 2, row3 ! 2, row3 ! 0, row2 ! 3])"

definition skinny_64_192_lfsr_component1 :: "4 word \<Rightarrow> 4 word" where
  "skinny_64_192_lfsr_component1 c = xor (push_bit 1 c) (and (xor (drop_bit 3 c) (drop_bit 2 c)) 1)"

definition skinny_64_192_lfsr_component2 :: "4 word \<Rightarrow> 4 word" where
  "skinny_64_192_lfsr_component2 c = xor (drop_bit 1 c) (xor (push_bit 3 c) (and c 0x8))"

definition skinny_64_192_update_tweakey_state ::
  "4 word list list \<Rightarrow> (4 word list list \<times> 4 word list)" where
  "skinny_64_192_update_tweakey_state tweakey_state =
     (let twky0 = tweakey_state ! 0; twky1 = tweakey_state ! 1; twky2 = tweakey_state ! 2;
          pt0 = skinny_64_192_apply_pt twky0;
          pt1 = map skinny_64_192_lfsr_component1 (skinny_64_192_apply_pt twky1);
          pt2 = map skinny_64_192_lfsr_component2 (skinny_64_192_apply_pt twky2);
          round_key_material =
            map (\<lambda>p. xor (fst p) (snd p)) (zip (map (\<lambda>p. xor (fst p) (snd p)) (zip pt0 pt1)) pt2);
          new_twky0 = pt0 @ take 8 twky0;
          new_twky1 = pt1 @ take 8 twky1;
          new_twky2 = pt2 @ take 8 twky2
      in ([new_twky0, new_twky1, new_twky2], round_key_material))"

definition skinny_64_192_initial_round_key :: "4 word list list \<Rightarrow> 4 word list" where
  "skinny_64_192_initial_round_key tweakey_state =
     foldl (\<lambda>acc twky. map (\<lambda>p. xor (fst p) (snd p)) (zip acc (take 8 twky)))
           (replicate 8 (0 :: 4 word)) tweakey_state"

function skinny_64_192_generate_round_tweakeys_acc ::
  "4 word list list \<Rightarrow> nat \<Rightarrow> 4 word list list \<Rightarrow> 4 word list list" where
  "skinny_64_192_generate_round_tweakeys_acc tweakey_state round_index acc =
     (if round_index \<ge> skinny_64_192_rounds - 1 then acc
      else
        let (new_state, rkm) = skinny_64_192_update_tweakey_state tweakey_state
        in skinny_64_192_generate_round_tweakeys_acc new_state (round_index + 1) (acc @ [rkm]))"
  by pat_completeness auto

termination skinny_64_192_generate_round_tweakeys_acc
  by (relation "measure (\<lambda>(tweakey_state, round_index, acc). (skinny_64_192_rounds - 1) - round_index)")
     (auto simp: skinny_64_192_rounds_def)

definition skinny_64_192_generate_round_tweakeys :: "192 word \<Rightarrow> 4 word list list" where
  "skinny_64_192_generate_round_tweakeys master_key =
     (let tweakey_state = skinny_64_192_key_to_tweakey_state master_key;
          rk0 = skinny_64_192_initial_round_key tweakey_state
      in skinny_64_192_generate_round_tweakeys_acc tweakey_state 0 [rk0])"


subsection \<open>T4: Orchestration\<close>

definition skinny_64_192_encrypt_round ::
  "4 word list \<Rightarrow> nat \<Rightarrow> 4 word list \<Rightarrow> 4 word list" where
  "skinny_64_192_encrypt_round state round_index round_key_material =
     (let s1 = skinny_64_192_sub_cells state;
          rc = skinny_64_192_rc ! (round_index mod length skinny_64_192_rc);
          c0 = of_nat (rc mod 16) :: 4 word;
          c1 = of_nat ((rc div 16) mod 4) :: 4 word;
          s2 = s1[0 := xor (s1 ! 0) c0, 4 := xor (s1 ! 4) c1, 8 := xor (s1 ! 8) 2];
          s3 = map (\<lambda>p. xor (fst p) (snd p)) (zip (take 8 s2) round_key_material) @ drop 8 s2;
          s4 = skinny_64_192_shift_rows s3
      in skinny_64_192_mix_columns s4)"

definition skinny_64_192_decrypt_round ::
  "4 word list \<Rightarrow> nat \<Rightarrow> 4 word list \<Rightarrow> 4 word list" where
  "skinny_64_192_decrypt_round state round_index round_key_material =
     (let s1 = skinny_64_192_mix_columns_inv state;
          s2 = skinny_64_192_shift_rows_inv s1;
          s3 = map (\<lambda>p. xor (fst p) (snd p)) (zip (take 8 s2) round_key_material) @ drop 8 s2;
          rc = skinny_64_192_rc ! (round_index mod length skinny_64_192_rc);
          c0 = of_nat (rc mod 16) :: 4 word;
          c1 = of_nat ((rc div 16) mod 4) :: 4 word;
          s4 = s3[0 := xor (s3 ! 0) c0, 4 := xor (s3 ! 4) c1, 8 := xor (s3 ! 8) 2]
      in skinny_64_192_sub_cells_inv s4)"

function skinny_64_192_encrypt_rounds_iterate ::
  "4 word list \<Rightarrow> 4 word list list \<Rightarrow> nat \<Rightarrow> 4 word list" where
  "skinny_64_192_encrypt_rounds_iterate state round_keys i =
     (if i \<ge> skinny_64_192_rounds then state
      else skinny_64_192_encrypt_rounds_iterate
             (skinny_64_192_encrypt_round state i (round_keys ! i)) round_keys (i + 1))"
  by pat_completeness auto

termination skinny_64_192_encrypt_rounds_iterate
  by (relation "measure (\<lambda>(state, round_keys, i). skinny_64_192_rounds - i)")
     (auto simp: skinny_64_192_rounds_def)

function skinny_64_192_decrypt_rounds_iterate ::
  "4 word list \<Rightarrow> 4 word list list \<Rightarrow> nat \<Rightarrow> 4 word list" where
  "skinny_64_192_decrypt_rounds_iterate state round_keys i =
     (if i \<ge> skinny_64_192_rounds then state
      else
        let round_index = skinny_64_192_rounds - 1 - i
        in skinny_64_192_decrypt_rounds_iterate
             (skinny_64_192_decrypt_round state round_index (round_keys ! round_index)) round_keys (i + 1))"
  by pat_completeness auto

termination skinny_64_192_decrypt_rounds_iterate
  by (relation "measure (\<lambda>(state, round_keys, i). skinny_64_192_rounds - i)")
     (auto simp: skinny_64_192_rounds_def)

definition skinny_64_192_encrypt :: "64 word \<Rightarrow> 192 word \<Rightarrow> 64 word" where
  "skinny_64_192_encrypt plaintext master_key =
     (let round_keys = skinny_64_192_generate_round_tweakeys master_key;
          state0 = skinny_64_192_block_to_state plaintext;
          state1 = skinny_64_192_encrypt_rounds_iterate state0 round_keys 0
      in skinny_64_192_state_to_block state1)"

definition skinny_64_192_decrypt :: "64 word \<Rightarrow> 192 word \<Rightarrow> 64 word" where
  "skinny_64_192_decrypt ciphertext master_key =
     (let round_keys = skinny_64_192_generate_round_tweakeys master_key;
          state0 = skinny_64_192_block_to_state ciphertext;
          state1 = skinny_64_192_decrypt_rounds_iterate state0 round_keys 0
      in skinny_64_192_state_to_block state1)"


subsection \<open>Test Vectors\<close>

definition skinny_64_192_test_key1 :: "192 word" where
  "skinny_64_192_test_key1 = 0xED00C85B120D68618753E24BFD908F60B2DBB41B422DFCD0"

definition skinny_64_192_test_plaintext1 :: "64 word" where
  "skinny_64_192_test_plaintext1 = 0x530C61D35E8663C3"

definition skinny_64_192_test_ciphertext1 :: "64 word" where
  "skinny_64_192_test_ciphertext1 = 0xDD2CF1A8F330303C"

end
