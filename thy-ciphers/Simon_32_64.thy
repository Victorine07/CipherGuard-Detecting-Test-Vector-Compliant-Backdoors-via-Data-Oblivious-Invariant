theory Simon_32_64
  imports
    "HOL-Library.Word"
    "HOL.Bit_Operations"
begin




definition simon_32_64_word_size :: nat where
  "simon_32_64_word_size = 16"

definition simon_32_64_block_size :: nat where
  "simon_32_64_block_size = 32"

definition simon_32_64_key_size :: nat where
  "simon_32_64_key_size = 64"

definition simon_32_64_rounds :: nat where
  "simon_32_64_rounds = 32"

definition simon_32_64_key_words :: nat where
  "simon_32_64_key_words = 4"

definition simon_32_64_word_mask :: "16 word" where
  "simon_32_64_word_mask = (-1)"

definition simon_32_64_round_constant :: "16 word" where
  "simon_32_64_round_constant = 0xFFFC"

definition simon_32_64_z_sequence :: int where
  "simon_32_64_z_sequence = 0x19C3522FB386A45F"





definition simon_32_64_rol :: "16 word \<Rightarrow> nat \<Rightarrow> 16 word" where
  "simon_32_64_rol x r = word_rotl r x"

definition simon_32_64_ror :: "16 word \<Rightarrow> nat \<Rightarrow> 16 word" where
  "simon_32_64_ror x r = word_rotr r x"

definition simon_32_64_f :: "16 word \<Rightarrow> 16 word" where
  "simon_32_64_f x =
     (let s1 = simon_32_64_rol x 1;
          s8 = simon_32_64_rol x 8;
          s2 = simon_32_64_rol x 2
      in xor (and s1 s8) s2)"

definition simon_32_64_encrypt_round ::
  "16 word \<Rightarrow> (16 word \<times> 16 word) \<Rightarrow> (16 word \<times> 16 word)" where
  "simon_32_64_encrypt_round k xy =
     (let x = fst xy;
          y = snd xy;
          fx = simon_32_64_f x;
          new_x = xor (xor y fx) k;
          new_y = x
      in (new_x, new_y))"

definition simon_32_64_decrypt_round ::
  "16 word \<Rightarrow> (16 word \<times> 16 word) \<Rightarrow> (16 word \<times> 16 word)" where
  "simon_32_64_decrypt_round k xy =
     (let x = fst xy;
          y = snd xy;
          fy = simon_32_64_f y;
          new_x = y;
          new_y = xor (xor x fy) k
      in (new_x, new_y))"





definition simon_32_64_key_to_words ::
  "64 word \<Rightarrow> (16 word \<times> 16 word \<times> 16 word \<times> 16 word)" where
  "simon_32_64_key_to_words master_key =
     (let           k0 = ucast master_key;
          k1 = ucast (drop_bit 16 master_key);
          k2 = ucast (drop_bit 32 master_key);
          k3 = ucast (drop_bit 48 master_key)
      in (k0, k1, k2, k3))"


function simon_32_64_generate_round_keys_rec ::
  "16 word list \<Rightarrow> int \<Rightarrow> nat \<Rightarrow> 16 word list" where
  "simon_32_64_generate_round_keys_rec rk z i =
     (if i \<ge> simon_32_64_rounds then rk
      else
        let rk_im4 = rk ! (i - 4);
            rk_im1 = rk ! (i - 1);
            rk_im3 = rk ! (i - 3);
            rs_3 = simon_32_64_ror rk_im1 3;
            rs_4 = simon_32_64_ror rk_im1 4;
            rs_1_m3 = simon_32_64_ror rk_im3 1;
            tmp = xor rk_im4 (xor rs_3 (xor rk_im3 (xor rs_4 rs_1_m3)));
            const_bit = (if bit z 0 then (1 :: 16 word) else 0);
            new_k = xor simon_32_64_round_constant (xor const_bit tmp);
            z_next = (z div 2) + (z mod 2) * (2 ^ 61)
        in simon_32_64_generate_round_keys_rec (rk @ [new_k]) z_next (i + 1))"
  by pat_completeness auto

termination simon_32_64_generate_round_keys_rec
  apply (relation "measure (\<lambda>(rk, z, i). simon_32_64_rounds - i)")
  apply (auto simp: simon_32_64_rounds_def)
  done


definition simon_32_64_generate_round_keys :: "64 word \<Rightarrow> 16 word list" where
  "simon_32_64_generate_round_keys master_key =
     (let (k0, k1, k2, k3) = simon_32_64_key_to_words master_key;
          rk0 = [k0, k1, k2, k3]
      in simon_32_64_generate_round_keys_rec rk0 simon_32_64_z_sequence 4)"




definition simon_32_64_block_to_words :: "32 word \<Rightarrow> (16 word \<times> 16 word)" where
  "simon_32_64_block_to_words block =
     (let left = ucast (drop_bit 16 block);
          right = ucast block
      in (left, right))"

definition simon_32_64_words_to_block :: "16 word \<Rightarrow> 16 word \<Rightarrow> 32 word" where
  "simon_32_64_words_to_block left right =
     or (push_bit 16 (ucast left)) (ucast right)"

fun simon_32_64_encrypt_block_iter ::
  "(16 word \<times> 16 word) \<Rightarrow> 16 word list \<Rightarrow> (16 word \<times> 16 word)" where
  "simon_32_64_encrypt_block_iter state [] = state"
| "simon_32_64_encrypt_block_iter state (k # ks) =
     simon_32_64_encrypt_block_iter (simon_32_64_encrypt_round k state) ks"

definition simon_32_64_encrypt_block ::
  "32 word \<Rightarrow> 16 word list \<Rightarrow> 32 word" where
  "simon_32_64_encrypt_block plaintext round_keys =
     (let state = simon_32_64_block_to_words plaintext;
          final_state = simon_32_64_encrypt_block_iter state round_keys;
          left = fst final_state;
          right = snd final_state
      in simon_32_64_words_to_block left right)"

definition simon_32_64_decrypt_block ::
  "32 word \<Rightarrow> 16 word list \<Rightarrow> 32 word" where
  "simon_32_64_decrypt_block ciphertext round_keys =
     (let state = simon_32_64_block_to_words ciphertext;
          final_state = foldl (\<lambda>st k. simon_32_64_decrypt_round k st) state (rev round_keys);
          left = fst final_state;
          right = snd final_state
      in simon_32_64_words_to_block left right)"

definition simon_32_64_encrypt :: "32 word \<Rightarrow> 64 word \<Rightarrow> 32 word" where
  "simon_32_64_encrypt plaintext master_key =
     (let round_keys = simon_32_64_generate_round_keys master_key
      in simon_32_64_encrypt_block plaintext round_keys)"

definition simon_32_64_decrypt :: "32 word \<Rightarrow> 64 word \<Rightarrow> 32 word" where
  "simon_32_64_decrypt ciphertext master_key =
     (let round_keys = simon_32_64_generate_round_keys master_key
      in simon_32_64_decrypt_block ciphertext round_keys)"




definition simon_32_64_test_plaintext :: "32 word" where
  "simon_32_64_test_plaintext =
     simon_32_64_words_to_block 0x6565 0x6877"

definition simon_32_64_test_key :: "64 word" where
  "simon_32_64_test_key =
     (push_bit 48 (ucast (0x1918 :: 16 word)))
          + (push_bit 32 (ucast (0x1110 :: 16 word)))
          + (push_bit 16 (ucast (0x0908 :: 16 word)))
          + 0x0100"

definition simon_32_64_test_ciphertext :: "32 word" where
  "simon_32_64_test_ciphertext =
     simon_32_64_words_to_block 0xC69B 0xE9BB"


lemma simon_32_64_test_vector_encrypt_correct:
  "simon_32_64_encrypt simon_32_64_test_plaintext simon_32_64_test_key
   = simon_32_64_test_ciphertext"
  by eval

lemma simon_32_64_test_vector_decrypt_correct:
  "simon_32_64_decrypt simon_32_64_test_ciphertext simon_32_64_test_key
   = simon_32_64_test_plaintext"
  by eval

end
