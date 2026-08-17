theory Speck_64_96
  imports
    "HOL-Library.Word"
    "HOL.Bit_Operations"
begin


definition speck_64_96_word_size :: nat where
  "speck_64_96_word_size = 32"

definition speck_64_96_alpha :: nat where
  "speck_64_96_alpha = 8"

definition speck_64_96_beta :: nat where
  "speck_64_96_beta = 3"

definition speck_64_96_rounds :: nat where
  "speck_64_96_rounds = 26"



definition speck_64_96_rol :: "32 word \<Rightarrow> nat \<Rightarrow> 32 word" where
  "speck_64_96_rol x n =
     word_rotl (n mod speck_64_96_word_size) x"

definition speck_64_96_ror :: "32 word \<Rightarrow> nat \<Rightarrow> 32 word" where
  "speck_64_96_ror x n =
     word_rotr (n mod speck_64_96_word_size) x"

definition speck_64_96_encrypt_round ::
  "32 word \<Rightarrow> (32 word \<times> 32 word) \<Rightarrow> (32 word \<times> 32 word)" where
  "speck_64_96_encrypt_round k xy = (
    let (x, y) = xy;
        rs_x = speck_64_96_ror x speck_64_96_alpha;
        add_xy = rs_x + y;
        new_x = xor add_xy k;
        ls_y = speck_64_96_rol y speck_64_96_beta;
        new_y = xor ls_y new_x
    in (new_x, new_y))"

definition speck_64_96_decrypt_round_inverse ::
  "32 word \<Rightarrow> (32 word \<times> 32 word) \<Rightarrow> (32 word \<times> 32 word)" where
  "speck_64_96_decrypt_round_inverse k xy_new = (
    let (x, y) = xy_new;
        xor_xy = xor x y;
        new_y = speck_64_96_ror xor_xy speck_64_96_beta;
        xor_xk = xor x k;
        msub = xor_xk - new_y;
        new_x = speck_64_96_rol msub speck_64_96_alpha
    in (new_x, new_y))"



function speck_64_96_gen_key_schedule_rec ::
  "32 word list \<Rightarrow> 32 word list \<Rightarrow> nat \<Rightarrow> 32 word list" where
  "speck_64_96_gen_key_schedule_rec l_keys k_keys i = (
     if i \<ge> (speck_64_96_rounds - 1) then k_keys
     else
       let rc = word_of_nat i :: 32 word;
           l_idx = (if i \<ge> length l_keys then i mod length l_keys else i);
           (new_l, new_k) = speck_64_96_encrypt_round rc (l_keys ! l_idx, k_keys ! i)
       in speck_64_96_gen_key_schedule_rec (l_keys @ [new_l]) (k_keys @ [new_k]) (i + 1))"
  by pat_completeness auto

termination speck_64_96_gen_key_schedule_rec
  by (relation "measure (\<lambda>(l, k, i). (speck_64_96_rounds - 1) - i)") auto

definition speck_64_96_generate_key_schedule ::
  "32 word list \<Rightarrow> 32 word list" where
  "speck_64_96_generate_key_schedule initial_key_words = (
     let k0 = [initial_key_words ! 0];
         l0 = [initial_key_words ! 1, initial_key_words ! 2]
     in speck_64_96_gen_key_schedule_rec l0 k0 0)"



fun speck_64_96_encrypt_block ::
  "(32 word \<times> 32 word) \<Rightarrow> 32 word list \<Rightarrow> (32 word \<times> 32 word)" where
  "speck_64_96_encrypt_block state [] = state"
| "speck_64_96_encrypt_block state (k # ks) =
     speck_64_96_encrypt_block (speck_64_96_encrypt_round k state) ks"

fun speck_64_96_decrypt_block ::
  "(32 word \<times> 32 word) \<Rightarrow> 32 word list \<Rightarrow> (32 word \<times> 32 word)" where
  "speck_64_96_decrypt_block state ks =
     foldl (\<lambda>st_new k. speck_64_96_decrypt_round_inverse k st_new) state (rev ks)"

definition speck_64_96_block_to_words ::
  "64 word \<Rightarrow> (32 word \<times> 32 word)" where
  "speck_64_96_block_to_words block = (
     let x = ucast (drop_bit 32 block) :: 32 word;
         y = ucast block :: 32 word
     in (x, y))"

definition speck_64_96_words_to_block ::
  "(32 word \<times> 32 word) \<Rightarrow> 64 word" where
  "speck_64_96_words_to_block xy = (
     let (x, y) = xy
     in or (push_bit 32 (ucast x)) (ucast y))"

definition speck_64_96_key_to_words ::
  "96 word \<Rightarrow> 32 word list" where
  "speck_64_96_key_to_words master_key = [ucast master_key :: 32 word,
     ucast (drop_bit 32 master_key) :: 32 word,
     ucast (drop_bit 64 master_key) :: 32 word]"

definition speck_64_96_encrypt ::
  "64 word \<Rightarrow> 96 word \<Rightarrow> 64 word" where
  "speck_64_96_encrypt plaintext master_key = (
     let key_words = speck_64_96_key_to_words master_key;
         round_keys = speck_64_96_generate_key_schedule key_words;
         (x, y) = speck_64_96_block_to_words plaintext;
         (c_x, c_y) = speck_64_96_encrypt_block (x, y) round_keys
     in speck_64_96_words_to_block (c_x, c_y))"

definition speck_64_96_decrypt ::
  "64 word \<Rightarrow> 96 word \<Rightarrow> 64 word" where
  "speck_64_96_decrypt ciphertext master_key = (
     let key_words = speck_64_96_key_to_words master_key;
         round_keys = speck_64_96_generate_key_schedule key_words;
         (x, y) = speck_64_96_block_to_words ciphertext;
         (p_x, p_y) = speck_64_96_decrypt_block (x, y) round_keys
     in speck_64_96_words_to_block (p_x, p_y))"

end