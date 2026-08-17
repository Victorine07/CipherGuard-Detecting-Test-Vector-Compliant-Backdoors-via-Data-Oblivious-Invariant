theory Skinny_128_256
  imports
    "HOL-Library.Word"
    "HOL.Bit_Operations"
begin

section \<open>SKINNY 128-256 (TK2): Tiered Core Definitions\<close>

subsection \<open>T1: Constants\<close>

definition skinny_128_256_block_size :: nat where
  "skinny_128_256_block_size = 128"

definition skinny_128_256_key_size :: nat where
  "skinny_128_256_key_size = 256"

definition skinny_128_256_rounds :: nat where
  "skinny_128_256_rounds = 48"

definition skinny_128_256_tweakey_blocks :: nat where
  "skinny_128_256_tweakey_blocks = 2"

definition skinny_128_256_sbox :: "8 word list" where
  "skinny_128_256_sbox =
     [101, 76, 106, 66, 75, 99, 67, 107, 85, 117, 90, 122, 83, 115, 91, 123,
      53, 140, 58, 129, 137, 51, 128, 59, 149, 37, 152, 42, 144, 35, 153, 43,
      229, 204, 232, 193, 201, 224, 192, 233, 213, 245, 216, 248, 208, 240, 217, 249,
      165, 28, 168, 18, 27, 160, 19, 169, 5, 181, 10, 184, 3, 176, 11, 185,
      50, 136, 60, 133, 141, 52, 132, 61, 145, 34, 156, 44, 148, 36, 157, 45,
      98, 74, 108, 69, 77, 100, 68, 109, 82, 114, 92, 124, 84, 116, 93, 125,
      161, 26, 172, 21, 29, 164, 20, 173, 2, 177, 12, 188, 4, 180, 13, 189,
      225, 200, 236, 197, 205, 228, 196, 237, 209, 241, 220, 252, 212, 244, 221, 253,
      54, 142, 56, 130, 139, 48, 131, 57, 150, 38, 154, 40, 147, 32, 155, 41,
      102, 78, 104, 65, 73, 96, 64, 105, 86, 118, 88, 120, 80, 112, 89, 121,
      166, 30, 170, 17, 25, 163, 16, 171, 6, 182, 8, 186, 0, 179, 9, 187,
      230, 206, 234, 194, 203, 227, 195, 235, 214, 246, 218, 250, 211, 243, 219, 251,
      49, 138, 62, 134, 143, 55, 135, 63, 146, 33, 158, 46, 151, 39, 159, 47,
      97, 72, 110, 70, 79, 103, 71, 111, 81, 113, 94, 126, 87, 119, 95, 127,
      162, 24, 174, 22, 31, 167, 23, 175, 1, 178, 14, 190, 7, 183, 15, 191,
      226, 202, 238, 198, 207, 231, 199, 239, 210, 242, 222, 254, 215, 247, 223, 255]"

definition skinny_128_256_rc :: "nat list" where
  "skinny_128_256_rc =
     [0x01, 0x03, 0x07, 0x0F, 0x1F, 0x3E, 0x3D, 0x3B, 0x37, 0x2F,
      0x1E, 0x3C, 0x39, 0x33, 0x27, 0x0E, 0x1D, 0x3A, 0x35, 0x2B,
      0x16, 0x2C, 0x18, 0x30, 0x21, 0x02, 0x05, 0x0B, 0x17, 0x2E,
      0x1C, 0x38, 0x31, 0x23, 0x06, 0x0D, 0x1B, 0x36, 0x2D, 0x1A,
      0x34, 0x29, 0x12, 0x24, 0x08, 0x11, 0x22, 0x04, 0x09, 0x13,
      0x26, 0x0C, 0x19, 0x32, 0x25, 0x0A, 0x15, 0x2A, 0x14, 0x28,
      0x10, 0x20]"

text \<open>Derived inverse table (not independently specified by the cipher).\<close>

definition skinny_128_256_sbox_inv :: "8 word list" where
  "skinny_128_256_sbox_inv =
     [172, 232, 104, 60, 108, 56, 168, 236, 170, 174, 58, 62, 106, 110, 234, 238,
      166, 163, 51, 54, 102, 99, 227, 230, 225, 164, 97, 52, 49, 100, 161, 228,
      141, 201, 73, 29, 77, 25, 137, 205, 139, 143, 27, 31, 75, 79, 203, 207,
      133, 192, 64, 21, 69, 16, 128, 197, 130, 135, 18, 23, 66, 71, 194, 199,
      150, 147, 3, 6, 86, 83, 211, 214, 209, 148, 81, 4, 1, 84, 145, 212,
      156, 216, 88, 12, 92, 8, 152, 220, 154, 158, 10, 14, 90, 94, 218, 222,
      149, 208, 80, 5, 85, 0, 144, 213, 146, 151, 2, 7, 82, 87, 210, 215,
      157, 217, 89, 13, 93, 9, 153, 221, 155, 159, 11, 15, 91, 95, 219, 223,
      22, 19, 131, 134, 70, 67, 195, 198, 65, 20, 193, 132, 17, 68, 129, 196,
      28, 72, 200, 140, 76, 24, 136, 204, 26, 30, 138, 142, 74, 78, 202, 206,
      53, 96, 224, 165, 101, 48, 160, 229, 50, 55, 162, 167, 98, 103, 226, 231,
      61, 105, 233, 173, 109, 57, 169, 237, 59, 63, 171, 175, 107, 111, 235, 239,
      38, 35, 179, 182, 118, 115, 243, 246, 113, 36, 241, 180, 33, 116, 177, 244,
      44, 120, 248, 188, 124, 40, 184, 252, 42, 46, 186, 190, 122, 126, 250, 254,
      37, 112, 240, 181, 117, 32, 176, 245, 34, 39, 178, 183, 114, 119, 242, 247,
      45, 121, 249, 189, 125, 41, 185, 253, 43, 47, 187, 191, 123, 127, 251, 255]"


subsection \<open>T2: Primitives\<close>

definition skinny_128_256_sub_cells :: "8 word list \<Rightarrow> 8 word list" where
  "skinny_128_256_sub_cells state = map (\<lambda>c. skinny_128_256_sbox ! unat c) state"

definition skinny_128_256_sub_cells_inv :: "8 word list \<Rightarrow> 8 word list" where
  "skinny_128_256_sub_cells_inv state = map (\<lambda>c. skinny_128_256_sbox_inv ! unat c) state"

definition skinny_128_256_shift_rows :: "8 word list \<Rightarrow> 8 word list" where
  "skinny_128_256_shift_rows state =
     map (\<lambda>i. state ! i) [0, 1, 2, 3, 7, 4, 5, 6, 10, 11, 8, 9, 13, 14, 15, 12]"

definition skinny_128_256_shift_rows_inv :: "8 word list \<Rightarrow> 8 word list" where
  "skinny_128_256_shift_rows_inv state =
     map (\<lambda>i. state ! i) [0, 1, 2, 3, 5, 6, 7, 4, 10, 11, 8, 9, 15, 12, 13, 14]"

definition skinny_128_256_mix_columns :: "8 word list \<Rightarrow> 8 word list" where
  "skinny_128_256_mix_columns state =
     (let r0 = take 4 state;
          r1 = take 4 (drop 4 state);
          r2 = take 4 (drop 8 state);
          r3 = take 4 (drop 12 state);
          r0_xor_r2 = map (\<lambda>p. xor (fst p) (snd p)) (zip r0 r2);
          new_r0 = map (\<lambda>p. xor (fst p) (snd p)) (zip r0_xor_r2 r3);
          new_r2 = map (\<lambda>p. xor (fst p) (snd p)) (zip r1 r2)
      in new_r0 @ r0 @ new_r2 @ r0_xor_r2)"

definition skinny_128_256_mix_columns_inv :: "8 word list \<Rightarrow> 8 word list" where
  "skinny_128_256_mix_columns_inv state =
     (let r0 = take 4 state;
          r1 = take 4 (drop 4 state);
          r2 = take 4 (drop 8 state);
          r3 = take 4 (drop 12 state);
          new_r2 = map (\<lambda>p. xor (fst p) (snd p)) (zip r1 r3);
          new_r1 = map (\<lambda>p. xor (fst p) (snd p)) (zip r2 new_r2);
          new_r3 = map (\<lambda>p. xor (fst p) (snd p)) (zip r0 r3)
      in r1 @ new_r1 @ new_r2 @ new_r3)"


subsection \<open>T3: Structural Components (Tweakey schedule)\<close>

definition skinny_128_256_block_to_state :: "128 word \<Rightarrow> 8 word list" where
  "skinny_128_256_block_to_state block =
     map (\<lambda>i. ucast (drop_bit (128 - 8 * (i + 1)) block) :: 8 word) [0..<16]"

definition skinny_128_256_state_to_block :: "8 word list \<Rightarrow> 128 word" where
  "skinny_128_256_state_to_block state = foldl (\<lambda>acc c. or (push_bit 8 acc) (ucast c)) (0 :: 128 word) state"

definition skinny_128_256_key_to_tweakey_state :: "256 word \<Rightarrow> 8 word list list" where
  "skinny_128_256_key_to_tweakey_state master_key =
     map (\<lambda>z. skinny_128_256_block_to_state (ucast (drop_bit (128 * (1 - z)) master_key) :: 128 word)) [0, 1]"

definition skinny_128_256_apply_pt :: "8 word list \<Rightarrow> 8 word list" where
  "skinny_128_256_apply_pt twky =
     (let row2 = take 4 (drop 8 twky); row3 = take 4 (drop 12 twky)
      in [row2 ! 1, row3 ! 3, row2 ! 0, row3 ! 1] @ [row2 ! 2, row3 ! 2, row3 ! 0, row2 ! 3])"

definition skinny_128_256_lfsr_component1 :: "8 word \<Rightarrow> 8 word" where
  "skinny_128_256_lfsr_component1 c = xor (push_bit 1 c) (and (xor (drop_bit 7 c) (drop_bit 5 c)) 1)"

definition skinny_128_256_update_tweakey_state ::
  "8 word list list \<Rightarrow> (8 word list list \<times> 8 word list)" where
  "skinny_128_256_update_tweakey_state tweakey_state =
     (let twky0 = tweakey_state ! 0; twky1 = tweakey_state ! 1;
          pt0 = skinny_128_256_apply_pt twky0;
          pt1 = map skinny_128_256_lfsr_component1 (skinny_128_256_apply_pt twky1);
          round_key_material = map (\<lambda>p. xor (fst p) (snd p)) (zip pt0 pt1);
          new_twky0 = pt0 @ take 8 twky0;
          new_twky1 = pt1 @ take 8 twky1
      in ([new_twky0, new_twky1], round_key_material))"

definition skinny_128_256_initial_round_key :: "8 word list list \<Rightarrow> 8 word list" where
  "skinny_128_256_initial_round_key tweakey_state =
     foldl (\<lambda>acc twky. map (\<lambda>p. xor (fst p) (snd p)) (zip acc (take 8 twky)))
           (replicate 8 (0 :: 8 word)) tweakey_state"

function skinny_128_256_generate_round_tweakeys_acc ::
  "8 word list list \<Rightarrow> nat \<Rightarrow> 8 word list list \<Rightarrow> 8 word list list" where
  "skinny_128_256_generate_round_tweakeys_acc tweakey_state round_index acc =
     (if round_index \<ge> skinny_128_256_rounds - 1 then acc
      else
        let (new_state, rkm) = skinny_128_256_update_tweakey_state tweakey_state
        in skinny_128_256_generate_round_tweakeys_acc new_state (round_index + 1) (acc @ [rkm]))"
  by pat_completeness auto

termination skinny_128_256_generate_round_tweakeys_acc
  by (relation "measure (\<lambda>(tweakey_state, round_index, acc). (skinny_128_256_rounds - 1) - round_index)")
     (auto simp: skinny_128_256_rounds_def)

definition skinny_128_256_generate_round_tweakeys :: "256 word \<Rightarrow> 8 word list list" where
  "skinny_128_256_generate_round_tweakeys master_key =
     (let tweakey_state = skinny_128_256_key_to_tweakey_state master_key;
          rk0 = skinny_128_256_initial_round_key tweakey_state
      in skinny_128_256_generate_round_tweakeys_acc tweakey_state 0 [rk0])"


subsection \<open>T4: Orchestration\<close>

definition skinny_128_256_encrypt_round ::
  "8 word list \<Rightarrow> nat \<Rightarrow> 8 word list \<Rightarrow> 8 word list" where
  "skinny_128_256_encrypt_round state round_index round_key_material =
     (let s1 = skinny_128_256_sub_cells state;
          rc = skinny_128_256_rc ! (round_index mod length skinny_128_256_rc);
          c0 = of_nat (rc mod 16) :: 8 word;
          c1 = of_nat ((rc div 16) mod 4) :: 8 word;
          s2 = s1[0 := xor (s1 ! 0) c0, 4 := xor (s1 ! 4) c1, 8 := xor (s1 ! 8) 2];
          s3 = map (\<lambda>p. xor (fst p) (snd p)) (zip (take 8 s2) round_key_material) @ drop 8 s2;
          s4 = skinny_128_256_shift_rows s3
      in skinny_128_256_mix_columns s4)"

definition skinny_128_256_decrypt_round ::
  "8 word list \<Rightarrow> nat \<Rightarrow> 8 word list \<Rightarrow> 8 word list" where
  "skinny_128_256_decrypt_round state round_index round_key_material =
     (let s1 = skinny_128_256_mix_columns_inv state;
          s2 = skinny_128_256_shift_rows_inv s1;
          s3 = map (\<lambda>p. xor (fst p) (snd p)) (zip (take 8 s2) round_key_material) @ drop 8 s2;
          rc = skinny_128_256_rc ! (round_index mod length skinny_128_256_rc);
          c0 = of_nat (rc mod 16) :: 8 word;
          c1 = of_nat ((rc div 16) mod 4) :: 8 word;
          s4 = s3[0 := xor (s3 ! 0) c0, 4 := xor (s3 ! 4) c1, 8 := xor (s3 ! 8) 2]
      in skinny_128_256_sub_cells_inv s4)"

function skinny_128_256_encrypt_rounds_iterate ::
  "8 word list \<Rightarrow> 8 word list list \<Rightarrow> nat \<Rightarrow> 8 word list" where
  "skinny_128_256_encrypt_rounds_iterate state round_keys i =
     (if i \<ge> skinny_128_256_rounds then state
      else skinny_128_256_encrypt_rounds_iterate
             (skinny_128_256_encrypt_round state i (round_keys ! i)) round_keys (i + 1))"
  by pat_completeness auto

termination skinny_128_256_encrypt_rounds_iterate
  by (relation "measure (\<lambda>(state, round_keys, i). skinny_128_256_rounds - i)")
     (auto simp: skinny_128_256_rounds_def)

function skinny_128_256_decrypt_rounds_iterate ::
  "8 word list \<Rightarrow> 8 word list list \<Rightarrow> nat \<Rightarrow> 8 word list" where
  "skinny_128_256_decrypt_rounds_iterate state round_keys i =
     (if i \<ge> skinny_128_256_rounds then state
      else
        let round_index = skinny_128_256_rounds - 1 - i
        in skinny_128_256_decrypt_rounds_iterate
             (skinny_128_256_decrypt_round state round_index (round_keys ! round_index)) round_keys (i + 1))"
  by pat_completeness auto

termination skinny_128_256_decrypt_rounds_iterate
  by (relation "measure (\<lambda>(state, round_keys, i). skinny_128_256_rounds - i)")
     (auto simp: skinny_128_256_rounds_def)

definition skinny_128_256_encrypt :: "128 word \<Rightarrow> 256 word \<Rightarrow> 128 word" where
  "skinny_128_256_encrypt plaintext master_key =
     (let round_keys = skinny_128_256_generate_round_tweakeys master_key;
          state0 = skinny_128_256_block_to_state plaintext;
          state1 = skinny_128_256_encrypt_rounds_iterate state0 round_keys 0
      in skinny_128_256_state_to_block state1)"

definition skinny_128_256_decrypt :: "128 word \<Rightarrow> 256 word \<Rightarrow> 128 word" where
  "skinny_128_256_decrypt ciphertext master_key =
     (let round_keys = skinny_128_256_generate_round_tweakeys master_key;
          state0 = skinny_128_256_block_to_state ciphertext;
          state1 = skinny_128_256_decrypt_rounds_iterate state0 round_keys 0
      in skinny_128_256_state_to_block state1)"


subsection \<open>Test Vectors\<close>

definition skinny_128_256_test_key1 :: "256 word" where
  "skinny_128_256_test_key1 = 0x009CEC81605D4AC1D2AE9E3085D7A1F31AC123EBFC00FDDCF01046CEEDDFCAB3"

definition skinny_128_256_test_plaintext1 :: "128 word" where
  "skinny_128_256_test_plaintext1 = 0x3A0C47767A26A68DD382A695E7022E25"

definition skinny_128_256_test_ciphertext1 :: "128 word" where
  "skinny_128_256_test_ciphertext1 = 0xB731D98A4BDE147A7ED4A6F16B9B587F"

end
