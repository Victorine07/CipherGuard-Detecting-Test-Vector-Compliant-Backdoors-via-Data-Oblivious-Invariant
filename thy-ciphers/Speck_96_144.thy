theory Speck_96_144
  imports
    "HOL-Library.Word"
    "HOL.Bit_Operations"
begin


definition speck_96_144_word_size :: nat where
  "speck_96_144_word_size = 48"

definition speck_96_144_alpha :: nat where
  "speck_96_144_alpha = 8"

definition speck_96_144_beta :: nat where
  "speck_96_144_beta = 3"

definition speck_96_144_rounds :: nat where
  "speck_96_144_rounds = 29"



definition speck_96_144_rol :: "48 word \<Rightarrow> nat \<Rightarrow> 48 word" where
  "speck_96_144_rol x n =
     word_rotl (n mod speck_96_144_word_size) x"

definition speck_96_144_ror :: "48 word \<Rightarrow> nat \<Rightarrow> 48 word" where
  "speck_96_144_ror x n =
     word_rotr (n mod speck_96_144_word_size) x"

definition speck_96_144_encrypt_round ::
  "48 word \<Rightarrow> (48 word \<times> 48 word) \<Rightarrow> (48 word \<times> 48 word)" where
  "speck_96_144_encrypt_round k xy = (
    let (x, y) = xy;
        rs_x = speck_96_144_ror x speck_96_144_alpha;
        add_xy = rs_x + y;
        new_x = xor add_xy k;
        ls_y = speck_96_144_rol y speck_96_144_beta;
        new_y = xor ls_y new_x
    in (new_x, new_y))"

definition speck_96_144_decrypt_round_inverse ::
  "48 word \<Rightarrow> (48 word \<times> 48 word) \<Rightarrow> (48 word \<times> 48 word)" where
  "speck_96_144_decrypt_round_inverse k xy_new = (
    let (x, y) = xy_new;
        xor_xy = xor x y;
        new_y = speck_96_144_ror xor_xy speck_96_144_beta;
        xor_xk = xor x k;
        msub = xor_xk - new_y;
        new_x = speck_96_144_rol msub speck_96_144_alpha
    in (new_x, new_y))"



function speck_96_144_gen_key_schedule_rec ::
  "48 word list \<Rightarrow> 48 word list \<Rightarrow> nat \<Rightarrow> 48 word list" where
  "speck_96_144_gen_key_schedule_rec l_keys k_keys i = (
     if i \<ge> (speck_96_144_rounds - 1) then k_keys
     else
       let rc = word_of_nat i :: 48 word;
           l_idx = (if i \<ge> length l_keys then i mod length l_keys else i);
           (new_l, new_k) = speck_96_144_encrypt_round rc (l_keys ! l_idx, k_keys ! i)
       in speck_96_144_gen_key_schedule_rec (l_keys @ [new_l]) (k_keys @ [new_k]) (i + 1))"
  by pat_completeness auto

termination speck_96_144_gen_key_schedule_rec
  by (relation "measure (\<lambda>(l, k, i). (speck_96_144_rounds - 1) - i)") auto

definition speck_96_144_generate_key_schedule ::
  "48 word list \<Rightarrow> 48 word list" where
  "speck_96_144_generate_key_schedule initial_key_words = (
     let k0 = [initial_key_words ! 0];
         l0 = [initial_key_words ! 1, initial_key_words ! 2]
     in speck_96_144_gen_key_schedule_rec l0 k0 0)"



fun speck_96_144_encrypt_block ::
  "(48 word \<times> 48 word) \<Rightarrow> 48 word list \<Rightarrow> (48 word \<times> 48 word)" where
  "speck_96_144_encrypt_block state [] = state"
| "speck_96_144_encrypt_block state (k # ks) =
     speck_96_144_encrypt_block (speck_96_144_encrypt_round k state) ks"

fun speck_96_144_decrypt_block ::
  "(48 word \<times> 48 word) \<Rightarrow> 48 word list \<Rightarrow> (48 word \<times> 48 word)" where
  "speck_96_144_decrypt_block state ks =
     foldl (\<lambda>st_new k. speck_96_144_decrypt_round_inverse k st_new) state (rev ks)"

definition speck_96_144_block_to_words ::
  "96 word \<Rightarrow> (48 word \<times> 48 word)" where
  "speck_96_144_block_to_words block = (
     let x = ucast (drop_bit 48 block) :: 48 word;
         y = ucast block :: 48 word
     in (x, y))"

definition speck_96_144_words_to_block ::
  "(48 word \<times> 48 word) \<Rightarrow> 96 word" where
  "speck_96_144_words_to_block xy = (
     let (x, y) = xy
     in or (push_bit 48 (ucast x)) (ucast y))"

definition speck_96_144_key_to_words ::
  "144 word \<Rightarrow> 48 word list" where
  "speck_96_144_key_to_words master_key = [ucast master_key :: 48 word,
     ucast (drop_bit 48 master_key) :: 48 word,
     ucast (drop_bit 96 master_key) :: 48 word]"

definition speck_96_144_encrypt ::
  "96 word \<Rightarrow> 144 word \<Rightarrow> 96 word" where
  "speck_96_144_encrypt plaintext master_key = (
     let key_words = speck_96_144_key_to_words master_key;
         round_keys = speck_96_144_generate_key_schedule key_words;
         (x, y) = speck_96_144_block_to_words plaintext;
         (c_x, c_y) = speck_96_144_encrypt_block (x, y) round_keys
     in speck_96_144_words_to_block (c_x, c_y))"

definition speck_96_144_decrypt ::
  "96 word \<Rightarrow> 144 word \<Rightarrow> 96 word" where
  "speck_96_144_decrypt ciphertext master_key = (
     let key_words = speck_96_144_key_to_words master_key;
         round_keys = speck_96_144_generate_key_schedule key_words;
         (x, y) = speck_96_144_block_to_words ciphertext;
         (p_x, p_y) = speck_96_144_decrypt_block (x, y) round_keys
     in speck_96_144_words_to_block (p_x, p_y))"

end