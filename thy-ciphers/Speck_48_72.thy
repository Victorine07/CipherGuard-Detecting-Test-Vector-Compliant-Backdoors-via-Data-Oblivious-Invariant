theory Speck_48_72
  imports
    "HOL-Library.Word"
    "HOL.Bit_Operations"
begin


definition speck_48_72_word_size :: nat where
  "speck_48_72_word_size = 24"

definition speck_48_72_alpha :: nat where
  "speck_48_72_alpha = 8"

definition speck_48_72_beta :: nat where
  "speck_48_72_beta = 3"

definition speck_48_72_rounds :: nat where
  "speck_48_72_rounds = 22"



definition speck_48_72_rol :: "24 word \<Rightarrow> nat \<Rightarrow> 24 word" where
  "speck_48_72_rol x n =
     word_rotl (n mod speck_48_72_word_size) x"

definition speck_48_72_ror :: "24 word \<Rightarrow> nat \<Rightarrow> 24 word" where
  "speck_48_72_ror x n =
     word_rotr (n mod speck_48_72_word_size) x"

definition speck_48_72_encrypt_round ::
  "24 word \<Rightarrow> (24 word \<times> 24 word) \<Rightarrow> (24 word \<times> 24 word)" where
  "speck_48_72_encrypt_round k xy = (
    let (x, y) = xy;
        rs_x = speck_48_72_ror x speck_48_72_alpha;
        add_xy = rs_x + y;
        new_x = xor add_xy k;
        ls_y = speck_48_72_rol y speck_48_72_beta;
        new_y = xor ls_y new_x
    in (new_x, new_y))"

definition speck_48_72_decrypt_round_inverse ::
  "24 word \<Rightarrow> (24 word \<times> 24 word) \<Rightarrow> (24 word \<times> 24 word)" where
  "speck_48_72_decrypt_round_inverse k xy_new = (
    let (x, y) = xy_new;
        xor_xy = xor x y;
        new_y = speck_48_72_ror xor_xy speck_48_72_beta;
        xor_xk = xor x k;
        msub = xor_xk - new_y;
        new_x = speck_48_72_rol msub speck_48_72_alpha
    in (new_x, new_y))"



function speck_48_72_gen_key_schedule_rec ::
  "24 word list \<Rightarrow> 24 word list \<Rightarrow> nat \<Rightarrow> 24 word list" where
  "speck_48_72_gen_key_schedule_rec l_keys k_keys i = (
     if i \<ge> (speck_48_72_rounds - 1) then k_keys
     else
       let rc = word_of_nat i :: 24 word;
           l_idx = (if i \<ge> length l_keys then i mod length l_keys else i);
           (new_l, new_k) = speck_48_72_encrypt_round rc (l_keys ! l_idx, k_keys ! i)
       in speck_48_72_gen_key_schedule_rec (l_keys @ [new_l]) (k_keys @ [new_k]) (i + 1))"
  by pat_completeness auto

termination speck_48_72_gen_key_schedule_rec
  by (relation "measure (\<lambda>(l, k, i). (speck_48_72_rounds - 1) - i)") auto

definition speck_48_72_generate_key_schedule ::
  "24 word list \<Rightarrow> 24 word list" where
  "speck_48_72_generate_key_schedule initial_key_words = (
     let k0 = [initial_key_words ! 0];
         l0 = [initial_key_words ! 1, initial_key_words ! 2]
     in speck_48_72_gen_key_schedule_rec l0 k0 0)"



fun speck_48_72_encrypt_block ::
  "(24 word \<times> 24 word) \<Rightarrow> 24 word list \<Rightarrow> (24 word \<times> 24 word)" where
  "speck_48_72_encrypt_block state [] = state"
| "speck_48_72_encrypt_block state (k # ks) =
     speck_48_72_encrypt_block (speck_48_72_encrypt_round k state) ks"

fun speck_48_72_decrypt_block ::
  "(24 word \<times> 24 word) \<Rightarrow> 24 word list \<Rightarrow> (24 word \<times> 24 word)" where
  "speck_48_72_decrypt_block state ks =
     foldl (\<lambda>st_new k. speck_48_72_decrypt_round_inverse k st_new) state (rev ks)"

definition speck_48_72_block_to_words ::
  "48 word \<Rightarrow> (24 word \<times> 24 word)" where
  "speck_48_72_block_to_words block = (
     let x = ucast (drop_bit 24 block) :: 24 word;
         y = ucast block :: 24 word
     in (x, y))"

definition speck_48_72_words_to_block ::
  "(24 word \<times> 24 word) \<Rightarrow> 48 word" where
  "speck_48_72_words_to_block xy = (
     let (x, y) = xy
     in or (push_bit 24 (ucast x)) (ucast y))"

definition speck_48_72_key_to_words ::
  "72 word \<Rightarrow> 24 word list" where
  "speck_48_72_key_to_words master_key = [ucast master_key :: 24 word,
     ucast (drop_bit 24 master_key) :: 24 word,
     ucast (drop_bit 48 master_key) :: 24 word]"

definition speck_48_72_encrypt ::
  "48 word \<Rightarrow> 72 word \<Rightarrow> 48 word" where
  "speck_48_72_encrypt plaintext master_key = (
     let key_words = speck_48_72_key_to_words master_key;
         round_keys = speck_48_72_generate_key_schedule key_words;
         (x, y) = speck_48_72_block_to_words plaintext;
         (c_x, c_y) = speck_48_72_encrypt_block (x, y) round_keys
     in speck_48_72_words_to_block (c_x, c_y))"

definition speck_48_72_decrypt ::
  "48 word \<Rightarrow> 72 word \<Rightarrow> 48 word" where
  "speck_48_72_decrypt ciphertext master_key = (
     let key_words = speck_48_72_key_to_words master_key;
         round_keys = speck_48_72_generate_key_schedule key_words;
         (x, y) = speck_48_72_block_to_words ciphertext;
         (p_x, p_y) = speck_48_72_decrypt_block (x, y) round_keys
     in speck_48_72_words_to_block (p_x, p_y))"

end