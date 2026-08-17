theory Simon_48_96
  imports
    "HOL-Library.Word"
    "HOL.Bit_Operations"
begin




definition simon_48_96_word_size :: nat where
  "simon_48_96_word_size = 24"

definition simon_48_96_block_size :: nat where
  "simon_48_96_block_size = 48"

definition simon_48_96_key_size :: nat where
  "simon_48_96_key_size = 96"

definition simon_48_96_rounds :: nat where
  "simon_48_96_rounds = 36"

definition simon_48_96_key_words :: nat where
  "simon_48_96_key_words = 4"

definition simon_48_96_word_mask :: "24 word" where
  "simon_48_96_word_mask = (-1)"

definition simon_48_96_round_constant :: "24 word" where
  "simon_48_96_round_constant = 0xFFFFFC"

definition simon_48_96_z_sequence :: int where
  "simon_48_96_z_sequence = 0x16864FB8AD0C9F71"





definition simon_48_96_rol :: "24 word \<Rightarrow> nat \<Rightarrow> 24 word" where
  "simon_48_96_rol x r = word_rotl r x"

definition simon_48_96_ror :: "24 word \<Rightarrow> nat \<Rightarrow> 24 word" where
  "simon_48_96_ror x r = word_rotr r x"

definition simon_48_96_f :: "24 word \<Rightarrow> 24 word" where
  "simon_48_96_f x =
     (let s1 = simon_48_96_rol x 1;
          s8 = simon_48_96_rol x 8;
          s2 = simon_48_96_rol x 2
      in xor (and s1 s8) s2)"

definition simon_48_96_encrypt_round ::
  "24 word \<Rightarrow> (24 word \<times> 24 word) \<Rightarrow> (24 word \<times> 24 word)" where
  "simon_48_96_encrypt_round k xy =
     (let x = fst xy;
          y = snd xy;
          fx = simon_48_96_f x;
          new_x = xor (xor y fx) k;
          new_y = x
      in (new_x, new_y))"

definition simon_48_96_decrypt_round ::
  "24 word \<Rightarrow> (24 word \<times> 24 word) \<Rightarrow> (24 word \<times> 24 word)" where
  "simon_48_96_decrypt_round k xy =
     (let x = fst xy;
          y = snd xy;
          fy = simon_48_96_f y;
          new_x = y;
          new_y = xor (xor x fy) k
      in (new_x, new_y))"





definition simon_48_96_key_to_words ::
  "96 word \<Rightarrow> (24 word \<times> 24 word \<times> 24 word \<times> 24 word)" where
  "simon_48_96_key_to_words master_key =
     (let           k0 = ucast master_key;
          k1 = ucast (drop_bit 24 master_key);
          k2 = ucast (drop_bit 48 master_key);
          k3 = ucast (drop_bit 72 master_key)
      in (k0, k1, k2, k3))"


function simon_48_96_generate_round_keys_rec ::
  "24 word list \<Rightarrow> int \<Rightarrow> nat \<Rightarrow> 24 word list" where
  "simon_48_96_generate_round_keys_rec rk z i =
     (if i \<ge> simon_48_96_rounds then rk
      else
        let rk_im4 = rk ! (i - 4);
            rk_im1 = rk ! (i - 1);
            rk_im3 = rk ! (i - 3);
            rs_3 = simon_48_96_ror rk_im1 3;
            rs_4 = simon_48_96_ror rk_im1 4;
            rs_1_m3 = simon_48_96_ror rk_im3 1;
            tmp = xor rk_im4 (xor rs_3 (xor rk_im3 (xor rs_4 rs_1_m3)));
            const_bit = (if bit z 0 then (1 :: 24 word) else 0);
            new_k = xor simon_48_96_round_constant (xor const_bit tmp);
            z_next = (z div 2) + (z mod 2) * (2 ^ 61)
        in simon_48_96_generate_round_keys_rec (rk @ [new_k]) z_next (i + 1))"
  by pat_completeness auto

termination simon_48_96_generate_round_keys_rec
  apply (relation "measure (\<lambda>(rk, z, i). simon_48_96_rounds - i)")
  apply (auto simp: simon_48_96_rounds_def)
  done


definition simon_48_96_generate_round_keys :: "96 word \<Rightarrow> 24 word list" where
  "simon_48_96_generate_round_keys master_key =
     (let (k0, k1, k2, k3) = simon_48_96_key_to_words master_key;
          rk0 = [k0, k1, k2, k3]
      in simon_48_96_generate_round_keys_rec rk0 simon_48_96_z_sequence 4)"




definition simon_48_96_block_to_words :: "48 word \<Rightarrow> (24 word \<times> 24 word)" where
  "simon_48_96_block_to_words block =
     (let left = ucast (drop_bit 24 block);
          right = ucast block
      in (left, right))"

definition simon_48_96_words_to_block :: "24 word \<Rightarrow> 24 word \<Rightarrow> 48 word" where
  "simon_48_96_words_to_block left right =
     or (push_bit 24 (ucast left)) (ucast right)"

fun simon_48_96_encrypt_block_iter ::
  "(24 word \<times> 24 word) \<Rightarrow> 24 word list \<Rightarrow> (24 word \<times> 24 word)" where
  "simon_48_96_encrypt_block_iter state [] = state"
| "simon_48_96_encrypt_block_iter state (k # ks) =
     simon_48_96_encrypt_block_iter (simon_48_96_encrypt_round k state) ks"

definition simon_48_96_encrypt_block ::
  "48 word \<Rightarrow> 24 word list \<Rightarrow> 48 word" where
  "simon_48_96_encrypt_block plaintext round_keys =
     (let state = simon_48_96_block_to_words plaintext;
          final_state = simon_48_96_encrypt_block_iter state round_keys;
          left = fst final_state;
          right = snd final_state
      in simon_48_96_words_to_block left right)"

definition simon_48_96_decrypt_block ::
  "48 word \<Rightarrow> 24 word list \<Rightarrow> 48 word" where
  "simon_48_96_decrypt_block ciphertext round_keys =
     (let state = simon_48_96_block_to_words ciphertext;
          final_state = foldl (\<lambda>st k. simon_48_96_decrypt_round k st) state (rev round_keys);
          left = fst final_state;
          right = snd final_state
      in simon_48_96_words_to_block left right)"

definition simon_48_96_encrypt :: "48 word \<Rightarrow> 96 word \<Rightarrow> 48 word" where
  "simon_48_96_encrypt plaintext master_key =
     (let round_keys = simon_48_96_generate_round_keys master_key
      in simon_48_96_encrypt_block plaintext round_keys)"

definition simon_48_96_decrypt :: "48 word \<Rightarrow> 96 word \<Rightarrow> 48 word" where
  "simon_48_96_decrypt ciphertext master_key =
     (let round_keys = simon_48_96_generate_round_keys master_key
      in simon_48_96_decrypt_block ciphertext round_keys)"




definition simon_48_96_test_plaintext :: "48 word" where
  "simon_48_96_test_plaintext =
     simon_48_96_words_to_block 0x726963 0x20646E"

definition simon_48_96_test_key :: "96 word" where
  "simon_48_96_test_key =
     (push_bit 72 (ucast (0x1A1918 :: 24 word)))
          + (push_bit 48 (ucast (0x121110 :: 24 word)))
          + (push_bit 24 (ucast (0x0A0908 :: 24 word)))
          + 0x020100"

definition simon_48_96_test_ciphertext :: "48 word" where
  "simon_48_96_test_ciphertext =
     simon_48_96_words_to_block 0x6E06A5 0xACF156"


lemma simon_48_96_test_vector_encrypt_correct:
  "simon_48_96_encrypt simon_48_96_test_plaintext simon_48_96_test_key
   = simon_48_96_test_ciphertext"
  by eval

lemma simon_48_96_test_vector_decrypt_correct:
  "simon_48_96_decrypt simon_48_96_test_ciphertext simon_48_96_test_key
   = simon_48_96_test_plaintext"
  by eval

end
