theory Simon_128_192
  imports
    "HOL-Library.Word"
    "HOL.Bit_Operations"
begin




definition simon_128_192_word_size :: nat where
  "simon_128_192_word_size = 64"

definition simon_128_192_block_size :: nat where
  "simon_128_192_block_size = 128"

definition simon_128_192_key_size :: nat where
  "simon_128_192_key_size = 192"

definition simon_128_192_rounds :: nat where
  "simon_128_192_rounds = 69"

definition simon_128_192_key_words :: nat where
  "simon_128_192_key_words = 3"

definition simon_128_192_word_mask :: "64 word" where
  "simon_128_192_word_mask = (-1)"

definition simon_128_192_round_constant :: "64 word" where
  "simon_128_192_round_constant = 0xFFFFFFFFFFFFFFFC"

definition simon_128_192_z_sequence :: int where
  "simon_128_192_z_sequence = 0x3C2CE51207A635DB"





definition simon_128_192_rol :: "64 word \<Rightarrow> nat \<Rightarrow> 64 word" where
  "simon_128_192_rol x r = word_rotl r x"

definition simon_128_192_ror :: "64 word \<Rightarrow> nat \<Rightarrow> 64 word" where
  "simon_128_192_ror x r = word_rotr r x"

definition simon_128_192_f :: "64 word \<Rightarrow> 64 word" where
  "simon_128_192_f x =
     (let s1 = simon_128_192_rol x 1;
          s8 = simon_128_192_rol x 8;
          s2 = simon_128_192_rol x 2
      in xor (and s1 s8) s2)"

definition simon_128_192_encrypt_round ::
  "64 word \<Rightarrow> (64 word \<times> 64 word) \<Rightarrow> (64 word \<times> 64 word)" where
  "simon_128_192_encrypt_round k xy =
     (let x = fst xy;
          y = snd xy;
          fx = simon_128_192_f x;
          new_x = xor (xor y fx) k;
          new_y = x
      in (new_x, new_y))"

definition simon_128_192_decrypt_round ::
  "64 word \<Rightarrow> (64 word \<times> 64 word) \<Rightarrow> (64 word \<times> 64 word)" where
  "simon_128_192_decrypt_round k xy =
     (let x = fst xy;
          y = snd xy;
          fy = simon_128_192_f y;
          new_x = y;
          new_y = xor (xor x fy) k
      in (new_x, new_y))"





definition simon_128_192_key_to_words ::
  "192 word \<Rightarrow> (64 word \<times> 64 word \<times> 64 word)" where
  "simon_128_192_key_to_words master_key =
     (let           k0 = ucast master_key;
          k1 = ucast (drop_bit 64 master_key);
          k2 = ucast (drop_bit 128 master_key)
      in (k0, k1, k2))"


function simon_128_192_generate_round_keys_rec ::
  "64 word list \<Rightarrow> int \<Rightarrow> nat \<Rightarrow> 64 word list" where
  "simon_128_192_generate_round_keys_rec rk z i =
     (if i \<ge> simon_128_192_rounds then rk
      else
        let rk_im3 = rk ! (i - 3);
            rk_im1 = rk ! (i - 1);
            rs_3 = simon_128_192_ror rk_im1 3;
            rs_4 = simon_128_192_ror rk_im1 4;
            tmp = xor rk_im3 (xor rs_3 rs_4);
            const_bit = (if bit z 0 then (1 :: 64 word) else 0);
            new_k = xor simon_128_192_round_constant (xor const_bit tmp);
            z_next = (z div 2) + (z mod 2) * (2 ^ 61)
        in simon_128_192_generate_round_keys_rec (rk @ [new_k]) z_next (i + 1))"
  by pat_completeness auto

termination simon_128_192_generate_round_keys_rec
  apply (relation "measure (\<lambda>(rk, z, i). simon_128_192_rounds - i)")
  apply (auto simp: simon_128_192_rounds_def)
  done


definition simon_128_192_generate_round_keys :: "192 word \<Rightarrow> 64 word list" where
  "simon_128_192_generate_round_keys master_key =
     (let (k0, k1, k2) = simon_128_192_key_to_words master_key;
          rk0 = [k0, k1, k2]
      in simon_128_192_generate_round_keys_rec rk0 simon_128_192_z_sequence 3)"




definition simon_128_192_block_to_words :: "128 word \<Rightarrow> (64 word \<times> 64 word)" where
  "simon_128_192_block_to_words block =
     (let left = ucast (drop_bit 64 block);
          right = ucast block
      in (left, right))"

definition simon_128_192_words_to_block :: "64 word \<Rightarrow> 64 word \<Rightarrow> 128 word" where
  "simon_128_192_words_to_block left right =
     or (push_bit 64 (ucast left)) (ucast right)"

fun simon_128_192_encrypt_block_iter ::
  "(64 word \<times> 64 word) \<Rightarrow> 64 word list \<Rightarrow> (64 word \<times> 64 word)" where
  "simon_128_192_encrypt_block_iter state [] = state"
| "simon_128_192_encrypt_block_iter state (k # ks) =
     simon_128_192_encrypt_block_iter (simon_128_192_encrypt_round k state) ks"

definition simon_128_192_encrypt_block ::
  "128 word \<Rightarrow> 64 word list \<Rightarrow> 128 word" where
  "simon_128_192_encrypt_block plaintext round_keys =
     (let state = simon_128_192_block_to_words plaintext;
          final_state = simon_128_192_encrypt_block_iter state round_keys;
          left = fst final_state;
          right = snd final_state
      in simon_128_192_words_to_block left right)"

definition simon_128_192_decrypt_block ::
  "128 word \<Rightarrow> 64 word list \<Rightarrow> 128 word" where
  "simon_128_192_decrypt_block ciphertext round_keys =
     (let state = simon_128_192_block_to_words ciphertext;
          final_state = foldl (\<lambda>st k. simon_128_192_decrypt_round k st) state (rev round_keys);
          left = fst final_state;
          right = snd final_state
      in simon_128_192_words_to_block left right)"

definition simon_128_192_encrypt :: "128 word \<Rightarrow> 192 word \<Rightarrow> 128 word" where
  "simon_128_192_encrypt plaintext master_key =
     (let round_keys = simon_128_192_generate_round_keys master_key
      in simon_128_192_encrypt_block plaintext round_keys)"

definition simon_128_192_decrypt :: "128 word \<Rightarrow> 192 word \<Rightarrow> 128 word" where
  "simon_128_192_decrypt ciphertext master_key =
     (let round_keys = simon_128_192_generate_round_keys master_key
      in simon_128_192_decrypt_block ciphertext round_keys)"




definition simon_128_192_test_plaintext :: "128 word" where
  "simon_128_192_test_plaintext =
     simon_128_192_words_to_block 0x206572656874206E 0x6568772065626972"

definition simon_128_192_test_key :: "192 word" where
  "simon_128_192_test_key =
     (push_bit 128 (ucast (0x1716151413121110 :: 64 word)))
          + (push_bit 64 (ucast (0x0F0E0D0C0B0A0908 :: 64 word)))
          + 0x0706050403020100"

definition simon_128_192_test_ciphertext :: "128 word" where
  "simon_128_192_test_ciphertext =
     simon_128_192_words_to_block 0xC4AC61EFFCDC0D4F 0x6C9C8D6E2597B85B"


lemma simon_128_192_test_vector_encrypt_correct:
  "simon_128_192_encrypt simon_128_192_test_plaintext simon_128_192_test_key
   = simon_128_192_test_ciphertext"
  by eval

lemma simon_128_192_test_vector_decrypt_correct:
  "simon_128_192_decrypt simon_128_192_test_ciphertext simon_128_192_test_key
   = simon_128_192_test_plaintext"
  by eval

end
