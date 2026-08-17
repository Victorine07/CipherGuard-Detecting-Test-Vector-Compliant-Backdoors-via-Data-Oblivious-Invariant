theory Rectangle_64_128
  imports
    "HOL-Library.Word"
    "HOL.Bit_Operations"
begin

section \<open>RECTANGLE 64-128: Tiered Core Definitions\<close>

subsection \<open>T1: Constants\<close>

definition rectangle_64_128_word_size :: nat where
  "rectangle_64_128_word_size = 4"

definition rectangle_64_128_block_size :: nat where
  "rectangle_64_128_block_size = 64"

definition rectangle_64_128_key_size :: nat where
  "rectangle_64_128_key_size = 128"

definition rectangle_64_128_rounds :: nat where
  "rectangle_64_128_rounds = 25"

definition rectangle_64_128_sbox :: "4 word list" where
  "rectangle_64_128_sbox = [0x6, 0x5, 0xC, 0xA, 0x1, 0xE, 0x7, 0x9, 0xB, 0x0, 0x3, 0xD, 0x8, 0xF, 0x4, 0x2]"

definition rectangle_64_128_row_rotations :: "nat list" where
  "rectangle_64_128_row_rotations = [0, 1, 12, 13]"

definition rectangle_64_128_rc :: "nat list" where
  "rectangle_64_128_rc =
     [0x01, 0x02, 0x04, 0x09, 0x12, 0x05, 0x0B, 0x16,
      0x0C, 0x19, 0x13, 0x07, 0x0F, 0x1F, 0x1E, 0x1C,
      0x18, 0x11, 0x03, 0x06, 0x0D, 0x1B, 0x17, 0x0E, 0x1D]"

text \<open>Derived inverse table (not independently specified by the cipher).\<close>

definition rectangle_64_128_sbox_inv :: "4 word list" where
  "rectangle_64_128_sbox_inv = [0x9, 0x4, 0xF, 0xA, 0xE, 0x1, 0x0, 0x6, 0xC, 0x7, 0x3, 0x8, 0x2, 0xB, 0x5, 0xD]"


subsection \<open>T2: Primitives\<close>

function rectangle_64_128_sub_column_acc :: "64 word \<Rightarrow> nat \<Rightarrow> 64 word \<Rightarrow> 64 word" where
  "rectangle_64_128_sub_column_acc state j acc =
     (if j \<ge> 16 then acc
      else
        let b0 = (if bit state j then (1 :: 4 word) else 0);
            b1 = (if bit state (16 + j) then (1 :: 4 word) else 0);
            b2 = (if bit state (32 + j) then (1 :: 4 word) else 0);
            b3 = (if bit state (48 + j) then (1 :: 4 word) else 0);
            col = or b0 (or (push_bit 1 b1) (or (push_bit 2 b2) (push_bit 3 b3)));
            s = rectangle_64_128_sbox ! unat col;
            o0 = (if bit s 0 then push_bit j (1 :: 64 word) else 0);
            o1 = (if bit s 1 then push_bit (16 + j) (1 :: 64 word) else 0);
            o2 = (if bit s 2 then push_bit (32 + j) (1 :: 64 word) else 0);
            o3 = (if bit s 3 then push_bit (48 + j) (1 :: 64 word) else 0);
            placed = or o0 (or o1 (or o2 o3))
        in rectangle_64_128_sub_column_acc state (j + 1) (or acc placed))"
  by pat_completeness auto

termination rectangle_64_128_sub_column_acc
  by (relation "measure (\<lambda>(state, j, acc). 16 - j)") auto

definition rectangle_64_128_sub_column :: "64 word \<Rightarrow> 64 word" where
  "rectangle_64_128_sub_column state = rectangle_64_128_sub_column_acc state 0 0"

function rectangle_64_128_sub_column_inv_acc :: "64 word \<Rightarrow> nat \<Rightarrow> 64 word \<Rightarrow> 64 word" where
  "rectangle_64_128_sub_column_inv_acc state j acc =
     (if j \<ge> 16 then acc
      else
        let b0 = (if bit state j then (1 :: 4 word) else 0);
            b1 = (if bit state (16 + j) then (1 :: 4 word) else 0);
            b2 = (if bit state (32 + j) then (1 :: 4 word) else 0);
            b3 = (if bit state (48 + j) then (1 :: 4 word) else 0);
            col = or b0 (or (push_bit 1 b1) (or (push_bit 2 b2) (push_bit 3 b3)));
            s = rectangle_64_128_sbox_inv ! unat col;
            o0 = (if bit s 0 then push_bit j (1 :: 64 word) else 0);
            o1 = (if bit s 1 then push_bit (16 + j) (1 :: 64 word) else 0);
            o2 = (if bit s 2 then push_bit (32 + j) (1 :: 64 word) else 0);
            o3 = (if bit s 3 then push_bit (48 + j) (1 :: 64 word) else 0);
            placed = or o0 (or o1 (or o2 o3))
        in rectangle_64_128_sub_column_inv_acc state (j + 1) (or acc placed))"
  by pat_completeness auto

termination rectangle_64_128_sub_column_inv_acc
  by (relation "measure (\<lambda>(state, j, acc). 16 - j)") auto

definition rectangle_64_128_sub_column_inv :: "64 word \<Rightarrow> 64 word" where
  "rectangle_64_128_sub_column_inv state = rectangle_64_128_sub_column_inv_acc state 0 0"

definition rectangle_64_128_shift_row :: "64 word \<Rightarrow> 64 word" where
  "rectangle_64_128_shift_row state =
     (let row0 = ucast state :: 16 word;
          row1 = ucast (drop_bit 16 state) :: 16 word;
          row2 = ucast (drop_bit 32 state) :: 16 word;
          row3 = ucast (drop_bit 48 state) :: 16 word;
          row0' = word_rotl 0 row0;
          row1' = word_rotl 1 row1;
          row2' = word_rotl 12 row2;
          row3' = word_rotl 13 row3
      in or (ucast row0')
            (or (push_bit 16 (ucast row1'))
                (or (push_bit 32 (ucast row2')) (push_bit 48 (ucast row3')))))"

definition rectangle_64_128_shift_row_inv :: "64 word \<Rightarrow> 64 word" where
  "rectangle_64_128_shift_row_inv state =
     (let row0 = ucast state :: 16 word;
          row1 = ucast (drop_bit 16 state) :: 16 word;
          row2 = ucast (drop_bit 32 state) :: 16 word;
          row3 = ucast (drop_bit 48 state) :: 16 word;
          row0' = word_rotr 0 row0;
          row1' = word_rotr 1 row1;
          row2' = word_rotr 12 row2;
          row3' = word_rotr 13 row3
      in or (ucast row0')
            (or (push_bit 16 (ucast row1'))
                (or (push_bit 32 (ucast row2')) (push_bit 48 (ucast row3')))))"


subsection \<open>T3: Structural Components (Key schedule)\<close>

function rectangle_64_128_sbox_columns_acc ::
  "32 word list \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> 32 word list \<Rightarrow> 32 word list" where
  "rectangle_64_128_sbox_columns_acc rows j num_cols acc =
     (if j \<ge> num_cols then acc
      else
        let b0 = (if bit (rows ! 0) j then (1 :: 4 word) else 0);
            b1 = (if bit (rows ! 1) j then (1 :: 4 word) else 0);
            b2 = (if bit (rows ! 2) j then (1 :: 4 word) else 0);
            b3 = (if bit (rows ! 3) j then (1 :: 4 word) else 0);
            col = or b0 (or (push_bit 1 b1) (or (push_bit 2 b2) (push_bit 3 b3)));
            s = rectangle_64_128_sbox ! unat col;
            clear_mask = not (push_bit j (1 :: 32 word));
            new0 = (if bit s 0 then or (acc ! 0) (push_bit j 1) else and (acc ! 0) clear_mask);
            new1 = (if bit s 1 then or (acc ! 1) (push_bit j 1) else and (acc ! 1) clear_mask);
            new2 = (if bit s 2 then or (acc ! 2) (push_bit j 1) else and (acc ! 2) clear_mask);
            new3 = (if bit s 3 then or (acc ! 3) (push_bit j 1) else and (acc ! 3) clear_mask);
            new_acc = [new0, new1, new2, new3]
        in rectangle_64_128_sbox_columns_acc rows (j + 1) num_cols new_acc)"
  by pat_completeness auto

termination rectangle_64_128_sbox_columns_acc
  by (relation "measure (\<lambda>(rows, j, num_cols, acc). num_cols - j)") auto

definition rectangle_64_128_apply_sbox_to_columns :: "32 word list \<Rightarrow> nat \<Rightarrow> 32 word list" where
  "rectangle_64_128_apply_sbox_to_columns rows num_cols =
     rectangle_64_128_sbox_columns_acc rows 0 num_cols (take 4 rows)"

definition rectangle_64_128_key_to_rows :: "128 word \<Rightarrow> 32 word list" where
  "rectangle_64_128_key_to_rows master_key =
     map (\<lambda>i. ucast (drop_bit (32 * i) master_key) :: 32 word) [0..<4]"

definition rectangle_64_128_update_key_rows :: "32 word list \<Rightarrow> nat \<Rightarrow> 32 word list" where
  "rectangle_64_128_update_key_rows rows round_index =
     (let sboxed = rectangle_64_128_apply_sbox_to_columns rows 8;
          r0 = sboxed ! 0; r1 = sboxed ! 1; r2 = sboxed ! 2; r3 = sboxed ! 3;
          new0 = xor (xor (word_rotl 8 r0) r1) (of_nat (rectangle_64_128_rc ! round_index));
          new1 = r2;
          new2 = xor (word_rotl 16 r2) r3;
          new3 = r0
      in [new0, new1, new2, new3])"

function rectangle_64_128_generate_round_keys_acc ::
  "32 word list \<Rightarrow> nat \<Rightarrow> 64 word list \<Rightarrow> 64 word list" where
  "rectangle_64_128_generate_round_keys_acc rows round_index acc =
     (let packed = or (ucast (and (rows ! 0) 0xFFFF))
                      (or (push_bit 16 (ucast (and (rows ! 1) 0xFFFF)))
                          (or (push_bit 32 (ucast (and (rows ! 2) 0xFFFF)))
                              (push_bit 48 (ucast (and (rows ! 3) 0xFFFF)))))
      in if round_index \<ge> rectangle_64_128_rounds then acc @ [packed]
         else rectangle_64_128_generate_round_keys_acc
                (rectangle_64_128_update_key_rows rows round_index) (round_index + 1) (acc @ [packed]))"
  by pat_completeness auto

termination rectangle_64_128_generate_round_keys_acc
  by (relation "measure (\<lambda>(rows, round_index, acc). rectangle_64_128_rounds - round_index)")
     (auto simp: rectangle_64_128_rounds_def)

definition rectangle_64_128_generate_round_keys :: "128 word \<Rightarrow> 64 word list" where
  "rectangle_64_128_generate_round_keys master_key =
     rectangle_64_128_generate_round_keys_acc (rectangle_64_128_key_to_rows master_key) 0 []"


subsection \<open>T4: Orchestration\<close>

definition rectangle_64_128_encrypt_round :: "64 word \<Rightarrow> 64 word \<Rightarrow> 64 word" where
  "rectangle_64_128_encrypt_round state round_key =
     rectangle_64_128_shift_row (rectangle_64_128_sub_column (xor state round_key))"

definition rectangle_64_128_decrypt_round :: "64 word \<Rightarrow> 64 word \<Rightarrow> 64 word" where
  "rectangle_64_128_decrypt_round state round_key =
     xor (rectangle_64_128_sub_column_inv (rectangle_64_128_shift_row_inv state)) round_key"

function rectangle_64_128_encrypt_rounds_iterate ::
  "64 word \<Rightarrow> 64 word list \<Rightarrow> nat \<Rightarrow> 64 word" where
  "rectangle_64_128_encrypt_rounds_iterate state round_keys i =
     (if i \<ge> rectangle_64_128_rounds then xor state (round_keys ! rectangle_64_128_rounds)
      else rectangle_64_128_encrypt_rounds_iterate
             (rectangle_64_128_encrypt_round state (round_keys ! i)) round_keys (i + 1))"
  by pat_completeness auto

termination rectangle_64_128_encrypt_rounds_iterate
  by (relation "measure (\<lambda>(state, round_keys, i). rectangle_64_128_rounds - i)")
     (auto simp: rectangle_64_128_rounds_def)

function rectangle_64_128_decrypt_rounds_iterate ::
  "64 word \<Rightarrow> 64 word list \<Rightarrow> nat \<Rightarrow> 64 word" where
  "rectangle_64_128_decrypt_rounds_iterate state round_keys i =
     (if i \<ge> rectangle_64_128_rounds then state
      else rectangle_64_128_decrypt_rounds_iterate
             (rectangle_64_128_decrypt_round state (round_keys ! (rectangle_64_128_rounds - 1 - i)))
             round_keys (i + 1))"
  by pat_completeness auto

termination rectangle_64_128_decrypt_rounds_iterate
  by (relation "measure (\<lambda>(state, round_keys, i). rectangle_64_128_rounds - i)")
     (auto simp: rectangle_64_128_rounds_def)

definition rectangle_64_128_encrypt :: "64 word \<Rightarrow> 128 word \<Rightarrow> 64 word" where
  "rectangle_64_128_encrypt plaintext master_key =
     (let round_keys = rectangle_64_128_generate_round_keys master_key
      in rectangle_64_128_encrypt_rounds_iterate plaintext round_keys 0)"

definition rectangle_64_128_decrypt :: "64 word \<Rightarrow> 128 word \<Rightarrow> 64 word" where
  "rectangle_64_128_decrypt ciphertext master_key =
     (let round_keys = rectangle_64_128_generate_round_keys master_key;
          state = xor ciphertext (round_keys ! rectangle_64_128_rounds)
      in rectangle_64_128_decrypt_rounds_iterate state round_keys 0)"


subsection \<open>Test Vectors\<close>

definition rectangle_64_128_test_key1 :: "128 word" where
  "rectangle_64_128_test_key1 = 0"

definition rectangle_64_128_test_plaintext1 :: "64 word" where
  "rectangle_64_128_test_plaintext1 = 0"

definition rectangle_64_128_test_ciphertext1 :: "64 word" where
  "rectangle_64_128_test_ciphertext1 = 0x99EE44A43613AEE6"

end
