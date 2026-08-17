theory lea_128_256
  imports
    "HOL-Library.Word"
    "HOL.Bit_Operations"
begin

text \<open>
  LEA-128/256 specification (128-bit block, 256-bit key, 32 rounds),
  matching the Python reference implementation and the official LEA equations.
\<close>


definition lea_128_256_word_size :: nat where
  "lea_128_256_word_size = 32"

definition lea_128_256_rounds :: nat where
  "lea_128_256_rounds = 32"

definition lea_128_256_m :: nat where
  "lea_128_256_m = 8"  (* number of key words *)

definition lea_128_256_delta :: "32 word list" where
  "lea_128_256_delta =
    [ 0xC3EFE9DB, 0x44626B02, 0x79E27C8A, 0x78DF30EC,
      0x715EA49E, 0xC785DA0A, 0xE04EF22A, 0xE5C40957 ]"


definition lea_128_256_rol :: "32 word \<Rightarrow> nat \<Rightarrow> 32 word" where
  "lea_128_256_rol x r = word_rotl r x"

definition lea_128_256_ror :: "32 word \<Rightarrow> nat \<Rightarrow> 32 word" where
  "lea_128_256_ror x r = word_rotr r x"


definition lea_128_256_extract_key_words :: "256 word \<Rightarrow> 32 word list" where
  "lea_128_256_extract_key_words k =
    [ ucast k,
      ucast (drop_bit 32 k),
      ucast (drop_bit 64 k),
      ucast (drop_bit 96 k),
      ucast (drop_bit 128 k),
      ucast (drop_bit 160 k),
      ucast (drop_bit 192 k),
      ucast (drop_bit 224 k) ]"

definition lea_128_256_step_key_expansion ::
  "32 word list \<Rightarrow> nat \<Rightarrow> (32 word list \<times> 32 word list)" where
  "lea_128_256_step_key_expansion T i = (
    let d = lea_128_256_delta ! (i mod 8);

        idx0 = (6 * i + 0) mod 8;
        idx1 = (6 * i + 1) mod 8;
        idx2 = (6 * i + 2) mod 8;
        idx3 = (6 * i + 3) mod 8;
        idx4 = (6 * i + 4) mod 8;
        idx5 = (6 * i + 5) mod 8;

        t0 = lea_128_256_rol (T ! idx0 + lea_128_256_rol d (i + 0)) 1;
        t1 = lea_128_256_rol (T ! idx1 + lea_128_256_rol d (i + 1)) 3;
        t2 = lea_128_256_rol (T ! idx2 + lea_128_256_rol d (i + 2)) 6;
        t3 = lea_128_256_rol (T ! idx3 + lea_128_256_rol d (i + 3)) 11;
        t4 = lea_128_256_rol (T ! idx4 + lea_128_256_rol d (i + 4)) 13;
        t5 = lea_128_256_rol (T ! idx5 + lea_128_256_rol d (i + 5)) 17;

        T1 = T[idx0 := t0];
        T2 = T1[idx1 := t1];
        T3 = T2[idx2 := t2];
        T4 = T3[idx3 := t3];
        T5 = T4[idx4 := t4];
        T6 = T5[idx5 := t5];

        rk = [t0, t1, t2, t3, t4, t5]
    in (rk, T6))"

function lea_128_256_gen_round_keys_iter ::
  "32 word list \<Rightarrow> nat \<Rightarrow> 32 word list list \<Rightarrow> 32 word list list" where
  "lea_128_256_gen_round_keys_iter T i acc = (
     if i \<ge> lea_128_256_rounds then acc
     else
       let (rk, T_next) = lea_128_256_step_key_expansion T i
       in lea_128_256_gen_round_keys_iter T_next (i + 1) (acc @ [rk]))"
  by pat_completeness auto

termination
  by (relation "measure (\<lambda>(T, i, acc). lea_128_256_rounds - i)") auto

definition lea_128_256_generate_round_keys :: "256 word \<Rightarrow> 32 word list list" where
  "lea_128_256_generate_round_keys key =
     lea_128_256_gen_round_keys_iter (lea_128_256_extract_key_words key) 0 []"



definition lea_128_256_encrypt_round ::
  "32 word list \<Rightarrow> 32 word list \<Rightarrow> 32 word list" where
  "lea_128_256_encrypt_round state rk = (
    let x0 = state ! 0;
        x1 = state ! 1;
        x2 = state ! 2;
        x3 = state ! 3;
        y0 = lea_128_256_rol ((xor x0 (rk ! 0)) + (xor x1 (rk ! 1))) 9;
        y1 = lea_128_256_ror ((xor x1 (rk ! 2)) + (xor x2 (rk ! 3))) 5;
        y2 = lea_128_256_ror ((xor x2 (rk ! 4)) + (xor x3 (rk ! 5))) 3;
        y3 = x0
    in [y0, y1, y2, y3])"

definition lea_128_256_decrypt_round ::
  "32 word list \<Rightarrow> 32 word list \<Rightarrow> 32 word list" where
  "lea_128_256_decrypt_round state rk = (
    let y0 = state ! 0;
        y1 = state ! 1;
        y2 = state ! 2;
        y3 = state ! 3;
        x0 = y3;
        x1 = xor (lea_128_256_ror y0 9 - (xor x0 (rk ! 0))) (rk ! 1);
        x2 = xor (lea_128_256_rol y1 5 - (xor x1 (rk ! 2))) (rk ! 3);
        x3 = xor (lea_128_256_rol y2 3 - (xor x2 (rk ! 4))) (rk ! 5)
    in [x0, x1, x2, x3])"


fun lea_128_256_encrypt_iter ::
  "32 word list \<Rightarrow> 32 word list list \<Rightarrow> 32 word list" where
  "lea_128_256_encrypt_iter st [] = st"
| "lea_128_256_encrypt_iter st (rk # rks) =
     lea_128_256_encrypt_iter (lea_128_256_encrypt_round st rk) rks"

fun lea_128_256_decrypt_iter ::
  "32 word list \<Rightarrow> 32 word list list \<Rightarrow> 32 word list" where
  "lea_128_256_decrypt_iter st rks =
     foldl lea_128_256_decrypt_round st (rev rks)"

definition lea_128_256_block_to_words :: "128 word \<Rightarrow> 32 word list" where
  "lea_128_256_block_to_words block =
    [ ucast block,
      ucast (drop_bit 32 block),
      ucast (drop_bit 64 block),
      ucast (drop_bit 96 block) ]"

definition lea_128_256_words_to_block :: "32 word list \<Rightarrow> 128 word" where
  "lea_128_256_words_to_block words =
    or (push_bit 96 (ucast (words ! 3)))
       (or (push_bit 64 (ucast (words ! 2)))
           (or (push_bit 32 (ucast (words ! 1)))
               (ucast (words ! 0))))"

definition lea_128_256_encrypt_block ::
  "128 word \<Rightarrow> 32 word list list \<Rightarrow> 128 word" where
  "lea_128_256_encrypt_block plaintext rks = (
    let state = lea_128_256_block_to_words plaintext;
        res = lea_128_256_encrypt_iter state rks
    in lea_128_256_words_to_block res)"

definition lea_128_256_decrypt_block ::
  "128 word \<Rightarrow> 32 word list list \<Rightarrow> 128 word" where
  "lea_128_256_decrypt_block ciphertext rks = (
    let state = lea_128_256_block_to_words ciphertext;
        res = lea_128_256_decrypt_iter state rks
    in lea_128_256_words_to_block res)"


definition lea_128_256_encrypt ::
  "128 word \<Rightarrow> 256 word \<Rightarrow> 128 word" where
  "lea_128_256_encrypt plaintext key =
     lea_128_256_encrypt_block plaintext (lea_128_256_generate_round_keys key)"

definition lea_128_256_decrypt ::
  "128 word \<Rightarrow> 256 word \<Rightarrow> 128 word" where
  "lea_128_256_decrypt ciphertext key =
     lea_128_256_decrypt_block ciphertext (lea_128_256_generate_round_keys key)"

end