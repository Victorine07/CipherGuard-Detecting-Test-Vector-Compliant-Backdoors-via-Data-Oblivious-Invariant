theory lea_128_192
  imports 
    "HOL-Library.Word" 
    "HOL.Bit_Operations"
begin

text \<open>
  LEA-128/192 specification (128-bit block, 192-bit key, 28 rounds),
  matching the Python reference implementation and the official LEA paper.
\<close>


definition lea_128_192_word_size :: nat where
  "lea_128_192_word_size = 32"

definition lea_128_192_rounds :: nat where
  "lea_128_192_rounds = 28"

definition lea_128_192_m :: nat where
  "lea_128_192_m = 6"  (* number of key words *)

(* Full LEA delta table (8 constants); LEA-192 uses delta[i mod 6] *)
definition lea_128_192_delta :: "32 word list" where
  "lea_128_192_delta = 
    [ 0xC3EFE9DB, 0x44626B02, 0x79E27C8A, 0x78DF30EC,
      0x715EA49E, 0xC785DA0A, 0xE04EF22A, 0xE5C40957 ]"


definition lea_128_192_rol :: "32 word \<Rightarrow> nat \<Rightarrow> 32 word" where
  "lea_128_192_rol x r = word_rotl r x"

definition lea_128_192_ror :: "32 word \<Rightarrow> nat \<Rightarrow> 32 word" where
  "lea_128_192_ror x r = word_rotr r x"



text \<open>
  For LEA-128/192, the master key is 192 bits, represented here as a 192-word.
  We extract 6 little-endian 32-bit words.
\<close>

definition lea_128_192_extract_key_words :: "192 word \<Rightarrow> 32 word list" where
  "lea_128_192_extract_key_words k = 
    [ ucast k,
      ucast (drop_bit 32 k),
      ucast (drop_bit 64 k),
      ucast (drop_bit 96 k),
      ucast (drop_bit 128 k),
      ucast (drop_bit 160 k) ]"

definition lea_128_192_step_key_expansion ::
  "32 word list \<Rightarrow> nat \<Rightarrow> (32 word list \<times> 32 word list)" where
  "lea_128_192_step_key_expansion T i = (
    let d  = lea_128_192_delta ! (i mod 6);
        t0 = lea_128_192_rol (T ! 0 + lea_128_192_rol d i)       1;
        t1 = lea_128_192_rol (T ! 1 + lea_128_192_rol d (i + 1)) 3;
        t2 = lea_128_192_rol (T ! 2 + lea_128_192_rol d (i + 2)) 6;
        t3 = lea_128_192_rol (T ! 3 + lea_128_192_rol d (i + 3)) 11;
        t4 = lea_128_192_rol (T ! 4 + lea_128_192_rol d (i + 4)) 13;
        t5 = lea_128_192_rol (T ! 5 + lea_128_192_rol d (i + 5)) 17;
        rk = [t0, t1, t2, t3, t4, t5]
    in (rk, [t0, t1, t2, t3, t4, t5]))"

function lea_128_192_gen_round_keys_iter ::
  "32 word list \<Rightarrow> nat \<Rightarrow> 32 word list list \<Rightarrow> 32 word list list" where
  "lea_128_192_gen_round_keys_iter T i acc = (
     if i \<ge> lea_128_192_rounds then acc
     else
       let (rk, T_next) = lea_128_192_step_key_expansion T i
       in lea_128_192_gen_round_keys_iter T_next (i + 1) (acc @ [rk]))"
  by pat_completeness auto

termination
  by (relation "measure (\<lambda>(T, i, acc). lea_128_192_rounds - i)") auto

definition lea_128_192_generate_round_keys :: "192 word \<Rightarrow> 32 word list list" where
  "lea_128_192_generate_round_keys key =
     lea_128_192_gen_round_keys_iter (lea_128_192_extract_key_words key) 0 []"


definition lea_128_192_encrypt_round ::
  "32 word list \<Rightarrow> 32 word list \<Rightarrow> 32 word list" where
  "lea_128_192_encrypt_round state rk = (
    let x0 = state ! 0;
        x1 = state ! 1;
        x2 = state ! 2;
        x3 = state ! 3;
        y0 = lea_128_192_rol ((xor x0 (rk ! 0)) + (xor x1 (rk ! 1))) 9;
        y1 = lea_128_192_ror ((xor x1 (rk ! 2)) + (xor x2 (rk ! 3))) 5;
        y2 = lea_128_192_ror ((xor x2 (rk ! 4)) + (xor x3 (rk ! 5))) 3;
        y3 = x0
    in [y0, y1, y2, y3])"

definition lea_128_192_decrypt_round ::
  "32 word list \<Rightarrow> 32 word list \<Rightarrow> 32 word list" where
  "lea_128_192_decrypt_round state rk = (
    let y0 = state ! 0;
        y1 = state ! 1;
        y2 = state ! 2;
        y3 = state ! 3;
        x0 = y3;
        x1 = xor (lea_128_192_ror y0 9 - (xor x0 (rk ! 0))) (rk ! 1);
        x2 = xor (lea_128_192_rol y1 5 - (xor x1 (rk ! 2))) (rk ! 3);
        x3 = xor (lea_128_192_rol y2 3 - (xor x2 (rk ! 4))) (rk ! 5)
    in [x0, x1, x2, x3])"


fun lea_128_192_encrypt_iter ::
  "32 word list \<Rightarrow> 32 word list list \<Rightarrow> 32 word list" where
  "lea_128_192_encrypt_iter st [] = st"
| "lea_128_192_encrypt_iter st (rk # rks) =
     lea_128_192_encrypt_iter (lea_128_192_encrypt_round st rk) rks"

fun lea_128_192_decrypt_iter ::
  "32 word list \<Rightarrow> 32 word list list \<Rightarrow> 32 word list" where
  "lea_128_192_decrypt_iter st rks =
     foldl lea_128_192_decrypt_round st (rev rks)"


definition lea_128_192_block_to_words :: "128 word \<Rightarrow> 32 word list" where
  "lea_128_192_block_to_words block =
    [ ucast block,
      ucast (drop_bit 32 block),
      ucast (drop_bit 64 block),
      ucast (drop_bit 96 block) ]"

definition lea_128_192_words_to_block :: "32 word list \<Rightarrow> 128 word" where
  "lea_128_192_words_to_block words =
    or (push_bit 96 (ucast (words ! 3)))
       (or (push_bit 64 (ucast (words ! 2)))
           (or (push_bit 32 (ucast (words ! 1)))
               (ucast (words ! 0))))"

definition lea_128_192_encrypt_block ::
  "128 word \<Rightarrow> 32 word list list \<Rightarrow> 128 word" where
  "lea_128_192_encrypt_block plaintext rks = (
    let state = lea_128_192_block_to_words plaintext;
        res = lea_128_192_encrypt_iter state rks
    in lea_128_192_words_to_block res)"

definition lea_128_192_decrypt_block ::
  "128 word \<Rightarrow> 32 word list list \<Rightarrow> 128 word" where
  "lea_128_192_decrypt_block ciphertext rks = (
    let state = lea_128_192_block_to_words ciphertext;
        res = lea_128_192_decrypt_iter state rks
    in lea_128_192_words_to_block res)"


definition lea_128_192_encrypt ::
  "128 word \<Rightarrow> 192 word \<Rightarrow> 128 word" where
  "lea_128_192_encrypt plaintext key =
     lea_128_192_encrypt_block plaintext (lea_128_192_generate_round_keys key)"

definition lea_128_192_decrypt ::
  "128 word \<Rightarrow> 192 word \<Rightarrow> 128 word" where
  "lea_128_192_decrypt ciphertext key =
     lea_128_192_decrypt_block ciphertext (lea_128_192_generate_round_keys key)"

end