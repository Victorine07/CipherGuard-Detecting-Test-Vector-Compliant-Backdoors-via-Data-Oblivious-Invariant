theory Hight_64_128
  imports
    "HOL-Library.Word"
    "HOL.Bit_Operations"
    "HOL.List"
begin

section \<open>HIGHT 64-128: Tiered Core Definitions\<close>

subsection \<open>T1: Constants\<close>

definition hight_64_128_block_size :: nat where
  "hight_64_128_block_size = 64"

definition hight_64_128_key_size :: nat where
  "hight_64_128_key_size = 128"

definition hight_64_128_block_bytes :: nat where
  "hight_64_128_block_bytes = 8"

definition hight_64_128_key_bytes :: nat where
  "hight_64_128_key_bytes = 16"

definition hight_64_128_internal_rounds :: nat where
  "hight_64_128_internal_rounds = 32"

definition hight_64_128_total_stages :: nat where
  "hight_64_128_total_stages = 34"

definition hight_64_128_byte_mask :: "8 word" where
  "hight_64_128_byte_mask = 0xFF"

definition hight_64_128_delta :: "8 word list" where
  "hight_64_128_delta = [
    0x5A, 0x6D, 0x36, 0x1B, 0x0D, 0x06, 0x03, 0x41,
    0x60, 0x30, 0x18, 0x4C, 0x66, 0x33, 0x59, 0x2C,
    0x56, 0x2B, 0x15, 0x4A, 0x65, 0x72, 0x39, 0x1C,
    0x4E, 0x67, 0x73, 0x79, 0x3C, 0x5E, 0x6F, 0x37,
    0x5B, 0x2D, 0x16, 0x0B, 0x05, 0x42, 0x21, 0x50,
    0x28, 0x54, 0x2A, 0x55, 0x6A, 0x75, 0x7A, 0x7D,
    0x3E, 0x5F, 0x2F, 0x17, 0x4B, 0x25, 0x52, 0x29,
    0x14, 0x0A, 0x45, 0x62, 0x31, 0x58, 0x6C, 0x76,
    0x3B, 0x1D, 0x0E, 0x47, 0x63, 0x71, 0x78, 0x7C,
    0x7E, 0x7F, 0x3F, 0x1F, 0x0F, 0x07, 0x43, 0x61,
    0x70, 0x38, 0x5C, 0x6E, 0x77, 0x7B, 0x3D, 0x1E,
    0x4F, 0x27, 0x53, 0x69, 0x34, 0x1A, 0x4D, 0x26,
    0x13, 0x49, 0x24, 0x12, 0x09, 0x04, 0x02, 0x01,
    0x40, 0x20, 0x10, 0x08, 0x44, 0x22, 0x11, 0x48,
    0x64, 0x32, 0x19, 0x0C, 0x46, 0x23, 0x51, 0x68,
    0x74, 0x3A, 0x5D, 0x2E, 0x57, 0x6B, 0x35, 0x5A]"

subsection \<open>T2: Primitives\<close>

definition hight_64_128_rol8 :: "8 word \<Rightarrow> nat \<Rightarrow> 8 word" where
  "hight_64_128_rol8 x n = word_rotl n x"

definition hight_64_128_ror8 :: "8 word \<Rightarrow> nat \<Rightarrow> 8 word" where
  "hight_64_128_ror8 x n = word_rotr n x"

definition hight_64_128_f0 :: "8 word \<Rightarrow> 8 word" where
  "hight_64_128_f0 x = xor (xor (hight_64_128_rol8 x 1) (hight_64_128_rol8 x 2)) (hight_64_128_rol8 x 7)"

definition hight_64_128_f1 :: "8 word \<Rightarrow> 8 word" where
  "hight_64_128_f1 x = xor (xor (hight_64_128_rol8 x 3) (hight_64_128_rol8 x 4)) (hight_64_128_rol8 x 6)"

definition hight_64_128_initial_transformation :: "8 word list \<Rightarrow> 8 word \<Rightarrow> 8 word \<Rightarrow> 8 word \<Rightarrow> 8 word \<Rightarrow> 8 word list" where
  "hight_64_128_initial_transformation state wk0 wk1 wk2 wk3 = [
    (state ! 0) + wk0,
    state ! 1,
    xor (state ! 2) wk1,
    state ! 3,
    (state ! 4) + wk2,
    state ! 5,
    xor (state ! 6) wk3,
    state ! 7]"

definition hight_64_128_encrypt_round :: "8 word list \<Rightarrow> 8 word \<Rightarrow> 8 word \<Rightarrow> 8 word \<Rightarrow> 8 word \<Rightarrow> 8 word list" where
  "hight_64_128_encrypt_round state sk0 sk1 sk2 sk3 = [
    xor (state ! 7) ((hight_64_128_f0 (state ! 6)) + sk3),
    state ! 0,
    (state ! 1) + (xor (hight_64_128_f1 (state ! 0)) sk0),
    state ! 2,
    xor (state ! 3) ((hight_64_128_f0 (state ! 2)) + sk1),
    state ! 4,
    (state ! 5) + (xor (hight_64_128_f1 (state ! 4)) sk2),
    state ! 6]"

definition hight_64_128_final_transformation :: "8 word list \<Rightarrow> 8 word \<Rightarrow> 8 word \<Rightarrow> 8 word \<Rightarrow> 8 word \<Rightarrow> 8 word list" where
  "hight_64_128_final_transformation state wk4 wk5 wk6 wk7 = [
    (state ! 1) + wk4,
    state ! 2,
    xor (state ! 3) wk5,
    state ! 4,
    (state ! 5) + wk6,
    state ! 6,
    xor (state ! 7) wk7,
    state ! 0]"

subsection \<open>T2: Decryption Primitives\<close>

definition hight_64_128_initial_transformation_inv ::
  "8 word list \<Rightarrow> 8 word \<Rightarrow> 8 word \<Rightarrow> 8 word \<Rightarrow> 8 word \<Rightarrow> 8 word list" where
  "hight_64_128_initial_transformation_inv state wk0 wk1 wk2 wk3 = [
    (state ! 0) - wk0,
    state ! 1,
    xor (state ! 2) wk1,
    state ! 3,
    (state ! 4) - wk2,
    state ! 5,
    xor (state ! 6) wk3,
    state ! 7]"

definition hight_64_128_decrypt_round ::
  "8 word list \<Rightarrow> 8 word \<Rightarrow> 8 word \<Rightarrow> 8 word \<Rightarrow> 8 word \<Rightarrow> 8 word list" where
  "hight_64_128_decrypt_round state sk0 sk1 sk2 sk3 = [
    state ! 1,
    (state ! 2) - (xor (hight_64_128_f1 (state ! 1)) sk0),
    state ! 3,
    xor (state ! 4) ((hight_64_128_f0 (state ! 3)) + sk1),
    state ! 5,
    (state ! 6) - (xor (hight_64_128_f1 (state ! 5)) sk2),
    state ! 7,
    xor (state ! 0) ((hight_64_128_f0 (state ! 7)) + sk3)]"

definition hight_64_128_final_transformation_inv ::
  "8 word list \<Rightarrow> 8 word \<Rightarrow> 8 word \<Rightarrow> 8 word \<Rightarrow> 8 word \<Rightarrow> 8 word list" where
  "hight_64_128_final_transformation_inv state wk4 wk5 wk6 wk7 = [
    state ! 7,
    (state ! 0) - wk4,
    state ! 1,
    xor (state ! 2) wk5,
    state ! 3,
    (state ! 4) - wk6,
    state ! 5,
    xor (state ! 6) wk7]"

subsection \<open>T3: Structural Components\<close>

definition hight_64_128_reverse_master_key :: "8 word list \<Rightarrow> 8 word list" where
  "hight_64_128_reverse_master_key MK = rev MK"

definition hight_64_128_initial_whitening_keys :: "8 word list \<Rightarrow> 8 word list" where
  "hight_64_128_initial_whitening_keys rMK = [rMK ! 12, rMK ! 13, rMK ! 14, rMK ! 15]"

definition hight_64_128_final_whitening_keys :: "8 word list \<Rightarrow> 8 word list" where
  "hight_64_128_final_whitening_keys rMK = [rMK ! 0, rMK ! 1, rMK ! 2, rMK ! 3]"

function hight_64_128_subkeys_for_round_scan :: "nat \<Rightarrow> nat \<Rightarrow> 8 word list \<Rightarrow> 8 word list" where
  "hight_64_128_subkeys_for_round_scan round_i idx rMK = (
    if idx \<ge> 64 then []
    else
      let i = idx div 8;
          j = idx mod 8;
          base = 4 * round_i
      in
        if base \<le> 16 * i + j \<and> 16 * i + j < base + 4 then
          ((rMK ! ((j + 8 - i) mod 8)) + (hight_64_128_delta ! (16 * i + j))) #
          hight_64_128_subkeys_for_round_scan round_i (idx + 1) rMK
        else if base \<le> (16 * i + j + 8) \<and> (16 * i + j + 8) < base + 4 then
          ((rMK ! (((j + 8 - i) mod 8) + 8)) + (hight_64_128_delta ! (16 * i + j + 8))) #
          hight_64_128_subkeys_for_round_scan round_i (idx + 1) rMK
        else
          hight_64_128_subkeys_for_round_scan round_i (idx + 1) rMK)"
  by pat_completeness auto
termination by (relation "measure (\<lambda>(round_i, idx, rMK). 64 - idx)") auto

definition hight_64_128_subkeys_for_round :: "8 word list \<Rightarrow> nat \<Rightarrow> 8 word list" where
  "hight_64_128_subkeys_for_round rMK round_i = hight_64_128_subkeys_for_round_scan round_i 0 rMK"

function hight_64_128_generate_round_keys_rec :: "nat \<Rightarrow> 8 word list \<Rightarrow> 8 word list" where
  "hight_64_128_generate_round_keys_rec round_i rMK = (
    if round_i \<ge> hight_64_128_internal_rounds then []
    else hight_64_128_subkeys_for_round rMK round_i @ hight_64_128_generate_round_keys_rec (round_i + 1) rMK)"
  by pat_completeness auto
termination by (relation "measure (\<lambda>(round_i, rMK). hight_64_128_internal_rounds - round_i)")
  (auto simp: hight_64_128_internal_rounds_def)

definition hight_64_128_generate_round_keys :: "8 word list \<Rightarrow> 8 word list" where
  "hight_64_128_generate_round_keys MK = (
    let rMK = hight_64_128_reverse_master_key MK
    in hight_64_128_initial_whitening_keys rMK @
       hight_64_128_generate_round_keys_rec 0 rMK @
       hight_64_128_final_whitening_keys rMK)"

subsection \<open>T4: Decryption Orchestration\<close>

definition hight_64_128_decrypt_rounds_step ::
  "8 word list \<Rightarrow> 8 word list \<Rightarrow> nat \<Rightarrow> 8 word list" where
  "hight_64_128_decrypt_rounds_step state round_keys round_i = (
    let base = 4 + 4 * round_i;
        sk0 = round_keys ! base;
        sk1 = round_keys ! (base + 1);
        sk2 = round_keys ! (base + 2);
        sk3 = round_keys ! (base + 3)
    in hight_64_128_decrypt_round state sk0 sk1 sk2 sk3)"

function hight_64_128_decrypt_rounds_iterate ::
  "8 word list \<Rightarrow> 8 word list \<Rightarrow> nat \<Rightarrow> 8 word list" where
  "hight_64_128_decrypt_rounds_iterate state round_keys i = (
    if i \<ge> hight_64_128_internal_rounds then state
    else
      let round_i = (hight_64_128_internal_rounds - 1) - i
      in hight_64_128_decrypt_rounds_iterate
           (hight_64_128_decrypt_rounds_step state round_keys round_i)
           round_keys
           (i + 1))"
  by pat_completeness auto
termination by (relation "measure (\<lambda>(state, round_keys, i). hight_64_128_internal_rounds - i)")
  (auto simp: hight_64_128_internal_rounds_def)

definition hight_64_128_decrypt_bytes :: "8 word list \<Rightarrow> 8 word list \<Rightarrow> 8 word list" where
  "hight_64_128_decrypt_bytes ciphertext MK = (
    let round_keys = hight_64_128_generate_round_keys MK;
        state0 = rev ciphertext;
        wk4 = round_keys ! 132;
        wk5 = round_keys ! 133;
        wk6 = round_keys ! 134;
        wk7 = round_keys ! 135;
        state1 = hight_64_128_final_transformation_inv state0 wk4 wk5 wk6 wk7;
        state2 = hight_64_128_decrypt_rounds_iterate state1 round_keys 0;
        wk0 = round_keys ! 0;
        wk1 = round_keys ! 1;
        wk2 = round_keys ! 2;
        wk3 = round_keys ! 3;
        state3 = hight_64_128_initial_transformation_inv state2 wk0 wk1 wk2 wk3
    in rev state3)"

subsection \<open>T4: Orchestration\<close>

definition hight_64_128_encrypt_rounds_step :: "8 word list \<Rightarrow> 8 word list \<Rightarrow> nat \<Rightarrow> 8 word list" where
  "hight_64_128_encrypt_rounds_step state round_keys round_i = (
    let base = 4 + 4 * round_i;
        sk0 = round_keys ! base;
        sk1 = round_keys ! (base + 1);
        sk2 = round_keys ! (base + 2);
        sk3 = round_keys ! (base + 3)
    in hight_64_128_encrypt_round state sk0 sk1 sk2 sk3)"

function hight_64_128_encrypt_rounds_iterate :: "8 word list \<Rightarrow> 8 word list \<Rightarrow> nat \<Rightarrow> 8 word list" where
  "hight_64_128_encrypt_rounds_iterate state round_keys round_i = (
    if round_i \<ge> hight_64_128_internal_rounds then state
    else hight_64_128_encrypt_rounds_iterate
           (hight_64_128_encrypt_rounds_step state round_keys round_i)
           round_keys
           (round_i + 1))"
  by pat_completeness auto
termination by (relation "measure (\<lambda>(state, round_keys, round_i). hight_64_128_internal_rounds - round_i)")
  (auto simp: hight_64_128_internal_rounds_def)

definition hight_64_128_encrypt_bytes :: "8 word list \<Rightarrow> 8 word list \<Rightarrow> 8 word list" where
  "hight_64_128_encrypt_bytes plaintext MK = (
    let round_keys = hight_64_128_generate_round_keys MK;
        state0 = rev plaintext;
        wk0 = round_keys ! 0;
        wk1 = round_keys ! 1;
        wk2 = round_keys ! 2;
        wk3 = round_keys ! 3;
        state1 = hight_64_128_initial_transformation state0 wk0 wk1 wk2 wk3;
        state2 = hight_64_128_encrypt_rounds_iterate state1 round_keys 0;
        wk4 = round_keys ! 132;
        wk5 = round_keys ! 133;
        wk6 = round_keys ! 134;
        wk7 = round_keys ! 135;
        state3 = hight_64_128_final_transformation state2 wk4 wk5 wk6 wk7
    in rev state3)"




subsection \<open>T4: Integer/Byte Wrappers\<close>

definition hight_64_128_block_to_bytes :: "64 word \<Rightarrow> 8 word list" where
  "hight_64_128_block_to_bytes block = [
    ucast (drop_bit 56 block),
    ucast (drop_bit 48 block),
    ucast (drop_bit 40 block),
    ucast (drop_bit 32 block),
    ucast (drop_bit 24 block),
    ucast (drop_bit 16 block),
    ucast (drop_bit 8 block),
    ucast block
  ]"

definition hight_64_128_bytes_to_block :: "8 word list \<Rightarrow> 64 word" where
  "hight_64_128_bytes_to_block bs =
    or (push_bit 56 (ucast (bs ! 0) :: 64 word))
      (or (push_bit 48 (ucast (bs ! 1) :: 64 word))
        (or (push_bit 40 (ucast (bs ! 2) :: 64 word))
          (or (push_bit 32 (ucast (bs ! 3) :: 64 word))
            (or (push_bit 24 (ucast (bs ! 4) :: 64 word))
              (or (push_bit 16 (ucast (bs ! 5) :: 64 word))
                (or (push_bit 8 (ucast (bs ! 6) :: 64 word))
                    (ucast (bs ! 7) :: 64 word)))))))"



definition hight_64_128_int_to_key_bytes :: "128 word \<Rightarrow> 8 word list" where
  "hight_64_128_int_to_key_bytes k = [
    ucast (drop_bit 120 k),
    ucast (drop_bit 112 k),
    ucast (drop_bit 104 k),
    ucast (drop_bit 96 k),
    ucast (drop_bit 88 k),
    ucast (drop_bit 80 k),
    ucast (drop_bit 72 k),
    ucast (drop_bit 64 k),
    ucast (drop_bit 56 k),
    ucast (drop_bit 48 k),
    ucast (drop_bit 40 k),
    ucast (drop_bit 32 k),
    ucast (drop_bit 24 k),
    ucast (drop_bit 16 k),
    ucast (drop_bit 8 k),
    ucast k
  ]"


definition hight_64_128_encrypt :: "64 word \<Rightarrow> 128 word \<Rightarrow> 64 word" where
  "hight_64_128_encrypt plaintext master_key =
    hight_64_128_bytes_to_block
      (hight_64_128_encrypt_bytes
        (hight_64_128_block_to_bytes plaintext)
        (hight_64_128_int_to_key_bytes master_key))"

definition hight_64_128_decrypt :: "64 word \<Rightarrow> 128 word \<Rightarrow> 64 word" where
  "hight_64_128_decrypt ciphertext master_key =
    hight_64_128_bytes_to_block
      (hight_64_128_decrypt_bytes
        (hight_64_128_block_to_bytes ciphertext)
        (hight_64_128_int_to_key_bytes master_key))"

subsection \<open>Test Vectors\<close>

subsection \<open>Test Vectors\<close>

subsection \<open>Test Vectors\<close>

definition hight_tv1_plaintext :: "8 word list" where
  "hight_tv1_plaintext = [
    0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00
  ]"

definition hight_tv1_key :: "8 word list" where
  "hight_tv1_key = [
    0x00, 0x11, 0x22, 0x33, 0x44, 0x55, 0x66, 0x77,
    0x88, 0x99, 0xaa, 0xbb, 0xcc, 0xdd, 0xee, 0xff
  ]"

definition hight_tv1_ciphertext_expected :: "8 word list" where
  "hight_tv1_ciphertext_expected = [
    0x00, 0xf4, 0x18, 0xae, 0xd9, 0x4f, 0x03, 0xf2
  ]"

definition hight_tv2_plaintext :: "8 word list" where
  "hight_tv2_plaintext = [
    0x00, 0x11, 0x22, 0x33, 0x44, 0x55, 0x66, 0x77
  ]"

definition hight_tv2_key :: "8 word list" where
  "hight_tv2_key = [
    0xff, 0xee, 0xdd, 0xcc, 0xbb, 0xaa, 0x99, 0x88,
    0x77, 0x66, 0x55, 0x44, 0x33, 0x22, 0x11, 0x00
  ]"

definition hight_tv2_ciphertext_expected :: "8 word list" where
  "hight_tv2_ciphertext_expected = [
    0x23, 0xce, 0x9f, 0x72, 0xe5, 0x43, 0xe6, 0xd8
  ]"

text \<open>Direct executable checks (byte-level API)\<close>

value "hight_64_128_encrypt_bytes hight_tv1_plaintext hight_tv1_key"
value "hight_tv1_ciphertext_expected"

value "hight_64_128_decrypt_bytes hight_tv1_ciphertext_expected hight_tv1_key"
value "hight_tv1_plaintext"

value "hight_64_128_encrypt_bytes hight_tv2_plaintext hight_tv2_key"
value "hight_tv2_ciphertext_expected"

value "hight_64_128_decrypt_bytes hight_tv2_ciphertext_expected hight_tv2_key"
value "hight_tv2_plaintext"

text \<open>Step-by-step debug chain for TV1 using existing names\<close>

(* Round keys *)
definition hight_tv1_round_keys :: "8 word list" where
  "hight_tv1_round_keys = hight_64_128_generate_round_keys hight_tv1_key"

(* Whitening keys extracted from round_keys, using your indexing scheme *)
definition hight_tv1_wk0 :: "8 word" where "hight_tv1_wk0 = hight_tv1_round_keys ! 0"
definition hight_tv1_wk1 :: "8 word" where "hight_tv1_wk1 = hight_tv1_round_keys ! 1"
definition hight_tv1_wk2 :: "8 word" where "hight_tv1_wk2 = hight_tv1_round_keys ! 2"
definition hight_tv1_wk3 :: "8 word" where "hight_tv1_wk3 = hight_tv1_round_keys ! 3"

definition hight_tv1_wk4 :: "8 word" where "hight_tv1_wk4 = hight_tv1_round_keys ! 132"
definition hight_tv1_wk5 :: "8 word" where "hight_tv1_wk5 = hight_tv1_round_keys ! 133"
definition hight_tv1_wk6 :: "8 word" where "hight_tv1_wk6 = hight_tv1_round_keys ! 134"
definition hight_tv1_wk7 :: "8 word" where "hight_tv1_wk7 = hight_tv1_round_keys ! 135"

(* Initial state after your rev + initial_transformation *)
definition hight_tv1_state0 :: "8 word list" where
  "hight_tv1_state0 = rev hight_tv1_plaintext"

definition hight_tv1_state1 :: "8 word list" where
  "hight_tv1_state1 =
     hight_64_128_initial_transformation
       hight_tv1_state0
       hight_tv1_wk0 hight_tv1_wk1 hight_tv1_wk2 hight_tv1_wk3"

(* First few encryption rounds using your encrypt_rounds_step *)
definition hight_tv1_state2 :: "8 word list" where
  "hight_tv1_state2 =
     hight_64_128_encrypt_rounds_step hight_tv1_state1 hight_tv1_round_keys 0"

definition hight_tv1_state3 :: "8 word list" where
  "hight_tv1_state3 =
     hight_64_128_encrypt_rounds_step hight_tv1_state2 hight_tv1_round_keys 1"

definition hight_tv1_state4 :: "8 word list" where
  "hight_tv1_state4 =
     hight_64_128_encrypt_rounds_step hight_tv1_state3 hight_tv1_round_keys 2"

(* Final transformation and ciphertext *)
definition hight_tv1_state_final :: "8 word list" where
  "hight_tv1_state_final =
     hight_64_128_final_transformation
       (hight_64_128_encrypt_rounds_iterate hight_tv1_state1 hight_tv1_round_keys 0)
       hight_tv1_wk4 hight_tv1_wk5 hight_tv1_wk6 hight_tv1_wk7"

definition hight_tv1_ciphertext_computed :: "8 word list" where
  "hight_tv1_ciphertext_computed = rev hight_tv1_state_final"

value "take 16 hight_tv1_round_keys"
value "hight_tv1_state0"
value "hight_tv1_state1"
value "hight_tv1_state2"
value "hight_tv1_state3"
value "hight_tv1_state4"
value "hight_64_128_encrypt_bytes hight_tv1_plaintext hight_tv1_key"
value "hight_tv1_ciphertext_computed"
value "hight_tv1_ciphertext_expected"

end