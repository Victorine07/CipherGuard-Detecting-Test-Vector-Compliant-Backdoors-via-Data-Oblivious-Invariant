theory Speck_32_64
  imports
    "HOL-Library.Word"
    "HOL.Bit_Operations"
begin


definition speck_32_64_word_size :: nat where
  "speck_32_64_word_size = 16"

definition speck_32_64_alpha :: nat where
  "speck_32_64_alpha = 7"

definition speck_32_64_beta :: nat where
  "speck_32_64_beta = 2"

definition speck_32_64_rounds :: nat where
  "speck_32_64_rounds = 22"



definition speck_32_64_rol :: "16 word \<Rightarrow> nat \<Rightarrow> 16 word" where
  "speck_32_64_rol x n =
     word_rotl (n mod speck_32_64_word_size) x"

definition speck_32_64_ror :: "16 word \<Rightarrow> nat \<Rightarrow> 16 word" where
  "speck_32_64_ror x n =
     word_rotr (n mod speck_32_64_word_size) x"

definition speck_32_64_encrypt_round ::
  "16 word \<Rightarrow> (16 word \<times> 16 word) \<Rightarrow> (16 word \<times> 16 word)" where
  "speck_32_64_encrypt_round k xy = (
    let (x, y) = xy;
        rs_x = speck_32_64_ror x speck_32_64_alpha;
        add_xy = rs_x + y;
        new_x = xor add_xy k;
        ls_y = speck_32_64_rol y speck_32_64_beta;
        new_y = xor ls_y new_x
    in (new_x, new_y))"

definition speck_32_64_decrypt_round_inverse ::
  "16 word \<Rightarrow> (16 word \<times> 16 word) \<Rightarrow> (16 word \<times> 16 word)" where
  "speck_32_64_decrypt_round_inverse k xy_new = (
    let (x, y) = xy_new;
        xor_xy = xor x y;
        new_y = speck_32_64_ror xor_xy speck_32_64_beta;
        xor_xk = xor x k;
        msub = xor_xk - new_y;
        new_x = speck_32_64_rol msub speck_32_64_alpha
    in (new_x, new_y))"



function speck_32_64_gen_key_schedule_rec ::
  "16 word list \<Rightarrow> 16 word list \<Rightarrow> nat \<Rightarrow> 16 word list" where
  "speck_32_64_gen_key_schedule_rec l_keys k_keys i = (
     if i \<ge> (speck_32_64_rounds - 1) then k_keys
     else
       let rc = word_of_nat i :: 16 word;
           l_idx = (if i \<ge> length l_keys then i mod length l_keys else i);
           (new_l, new_k) = speck_32_64_encrypt_round rc (l_keys ! l_idx, k_keys ! i)
       in speck_32_64_gen_key_schedule_rec (l_keys @ [new_l]) (k_keys @ [new_k]) (i + 1))"
  by pat_completeness auto

termination speck_32_64_gen_key_schedule_rec
  by (relation "measure (\<lambda>(l, k, i). (speck_32_64_rounds - 1) - i)") auto

definition speck_32_64_generate_key_schedule ::
  "16 word list \<Rightarrow> 16 word list" where
  "speck_32_64_generate_key_schedule initial_key_words = (
     let k0 = [initial_key_words ! 0];
         l0 = [initial_key_words ! 1, initial_key_words ! 2, initial_key_words ! 3]
     in speck_32_64_gen_key_schedule_rec l0 k0 0)"



fun speck_32_64_encrypt_block ::
  "(16 word \<times> 16 word) \<Rightarrow> 16 word list \<Rightarrow> (16 word \<times> 16 word)" where
  "speck_32_64_encrypt_block state [] = state"
| "speck_32_64_encrypt_block state (k # ks) =
     speck_32_64_encrypt_block (speck_32_64_encrypt_round k state) ks"

fun speck_32_64_decrypt_block ::
  "(16 word \<times> 16 word) \<Rightarrow> 16 word list \<Rightarrow> (16 word \<times> 16 word)" where
  "speck_32_64_decrypt_block state ks =
     foldl (\<lambda>st_new k. speck_32_64_decrypt_round_inverse k st_new) state (rev ks)"

definition speck_32_64_block_to_words ::
  "32 word \<Rightarrow> (16 word \<times> 16 word)" where
  "speck_32_64_block_to_words block = (
     let x = ucast (drop_bit 16 block) :: 16 word;
         y = ucast block :: 16 word
     in (x, y))"

definition speck_32_64_words_to_block ::
  "(16 word \<times> 16 word) \<Rightarrow> 32 word" where
  "speck_32_64_words_to_block xy = (
     let (x, y) = xy
     in or (push_bit 16 (ucast x)) (ucast y))"

definition speck_32_64_key_to_words ::
  "64 word \<Rightarrow> 16 word list" where
  "speck_32_64_key_to_words master_key = [ucast master_key :: 16 word,
     ucast (drop_bit 16 master_key) :: 16 word,
     ucast (drop_bit 32 master_key) :: 16 word,
     ucast (drop_bit 48 master_key) :: 16 word]"

definition speck_32_64_encrypt ::
  "32 word \<Rightarrow> 64 word \<Rightarrow> 32 word" where
  "speck_32_64_encrypt plaintext master_key = (
     let key_words = speck_32_64_key_to_words master_key;
         round_keys = speck_32_64_generate_key_schedule key_words;
         (x, y) = speck_32_64_block_to_words plaintext;
         (c_x, c_y) = speck_32_64_encrypt_block (x, y) round_keys
     in speck_32_64_words_to_block (c_x, c_y))"

definition speck_32_64_decrypt ::
  "32 word \<Rightarrow> 64 word \<Rightarrow> 32 word" where
  "speck_32_64_decrypt ciphertext master_key = (
     let key_words = speck_32_64_key_to_words master_key;
         round_keys = speck_32_64_generate_key_schedule key_words;
         (x, y) = speck_32_64_block_to_words ciphertext;
         (p_x, p_y) = speck_32_64_decrypt_block (x, y) round_keys
     in speck_32_64_words_to_block (p_x, p_y))"

end