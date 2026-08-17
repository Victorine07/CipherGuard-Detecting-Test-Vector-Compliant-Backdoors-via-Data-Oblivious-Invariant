theory Speck_128_128
  imports
    "HOL-Library.Word"
    "HOL.Bit_Operations"
begin


definition speck_128_128_word_size :: nat where
  "speck_128_128_word_size = 64"

definition speck_128_128_alpha :: nat where
  "speck_128_128_alpha = 8"

definition speck_128_128_beta :: nat where
  "speck_128_128_beta = 3"

definition speck_128_128_rounds :: nat where
  "speck_128_128_rounds = 32"



definition speck_128_128_rol :: "64 word \<Rightarrow> nat \<Rightarrow> 64 word" where
  "speck_128_128_rol x n =
     word_rotl (n mod speck_128_128_word_size) x"

definition speck_128_128_ror :: "64 word \<Rightarrow> nat \<Rightarrow> 64 word" where
  "speck_128_128_ror x n =
     word_rotr (n mod speck_128_128_word_size) x"

definition speck_128_128_encrypt_round ::
  "64 word \<Rightarrow> (64 word \<times> 64 word) \<Rightarrow> (64 word \<times> 64 word)" where
  "speck_128_128_encrypt_round k xy = (
    let (x, y) = xy;
        rs_x = speck_128_128_ror x speck_128_128_alpha;
        add_xy = rs_x + y;
        new_x = xor add_xy k;
        ls_y = speck_128_128_rol y speck_128_128_beta;
        new_y = xor ls_y new_x
    in (new_x, new_y))"

definition speck_128_128_decrypt_round_inverse ::
  "64 word \<Rightarrow> (64 word \<times> 64 word) \<Rightarrow> (64 word \<times> 64 word)" where
  "speck_128_128_decrypt_round_inverse k xy_new = (
    let (x, y) = xy_new;
        xor_xy = xor x y;
        new_y = speck_128_128_ror xor_xy speck_128_128_beta;
        xor_xk = xor x k;
        msub = xor_xk - new_y;
        new_x = speck_128_128_rol msub speck_128_128_alpha
    in (new_x, new_y))"


function speck_128_128_gen_key_schedule_rec ::
  "64 word list \<Rightarrow> 64 word list \<Rightarrow> nat \<Rightarrow> 64 word list" where
  "speck_128_128_gen_key_schedule_rec l_keys k_keys i = (
     if i \<ge> (speck_128_128_rounds - 1) then k_keys
     else
       let rc = word_of_nat i :: 64 word;
           l_idx = (if i \<ge> length l_keys then i mod length l_keys else i);
           (new_l, new_k) = speck_128_128_encrypt_round rc (l_keys ! l_idx, k_keys ! i)
       in speck_128_128_gen_key_schedule_rec (l_keys @ [new_l]) (k_keys @ [new_k]) (i + 1))"
  by pat_completeness auto

termination speck_128_128_gen_key_schedule_rec
  by (relation "measure (\<lambda>(l, k, i). (speck_128_128_rounds - 1) - i)") auto

definition speck_128_128_generate_key_schedule ::
  "64 word list \<Rightarrow> 64 word list" where
  "speck_128_128_generate_key_schedule initial_key_words = (
     let k0 = [initial_key_words ! 0];
         l0 = [initial_key_words ! 1]
     in speck_128_128_gen_key_schedule_rec l0 k0 0)"



fun speck_128_128_encrypt_block ::
  "(64 word \<times> 64 word) \<Rightarrow> 64 word list \<Rightarrow> (64 word \<times> 64 word)" where
  "speck_128_128_encrypt_block state [] = state"
| "speck_128_128_encrypt_block state (k # ks) =
     speck_128_128_encrypt_block (speck_128_128_encrypt_round k state) ks"

fun speck_128_128_decrypt_block ::
  "(64 word \<times> 64 word) \<Rightarrow> 64 word list \<Rightarrow> (64 word \<times> 64 word)" where
  "speck_128_128_decrypt_block state ks =
     foldl (\<lambda>st_new k. speck_128_128_decrypt_round_inverse k st_new) state (rev ks)"

definition speck_128_128_block_to_words ::
  "128 word \<Rightarrow> (64 word \<times> 64 word)" where
  "speck_128_128_block_to_words block = (
     let x = ucast (drop_bit 64 block) :: 64 word;
         y = ucast block :: 64 word
     in (x, y))"

definition speck_128_128_words_to_block ::
  "(64 word \<times> 64 word) \<Rightarrow> 128 word" where
  "speck_128_128_words_to_block xy = (
     let (x, y) = xy
     in or (push_bit 64 (ucast x)) (ucast y))"

definition speck_128_128_key_to_words ::
  "128 word \<Rightarrow> 64 word list" where
  "speck_128_128_key_to_words master_key = [ucast master_key :: 64 word,
     ucast (drop_bit 64 master_key) :: 64 word]"

definition speck_128_128_encrypt ::
  "128 word \<Rightarrow> 128 word \<Rightarrow> 128 word" where
  "speck_128_128_encrypt plaintext master_key = (
     let key_words = speck_128_128_key_to_words master_key;
         round_keys = speck_128_128_generate_key_schedule key_words;
         (x, y) = speck_128_128_block_to_words plaintext;
         (c_x, c_y) = speck_128_128_encrypt_block (x, y) round_keys
     in speck_128_128_words_to_block (c_x, c_y))"

definition speck_128_128_decrypt ::
  "128 word \<Rightarrow> 128 word \<Rightarrow> 128 word" where
  "speck_128_128_decrypt ciphertext master_key = (
     let key_words = speck_128_128_key_to_words master_key;
         round_keys = speck_128_128_generate_key_schedule key_words;
         (x, y) = speck_128_128_block_to_words ciphertext;
         (p_x, p_y) = speck_128_128_decrypt_block (x, y) round_keys
     in speck_128_128_words_to_block (p_x, p_y))"

end