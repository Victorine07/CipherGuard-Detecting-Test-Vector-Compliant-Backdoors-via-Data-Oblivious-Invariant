theory Simon_64_96
  imports
    "HOL-Library.Word"
    "HOL.Bit_Operations"
begin




definition simon_64_96_word_size :: nat where
  "simon_64_96_word_size = 32"

definition simon_64_96_block_size :: nat where
  "simon_64_96_block_size = 64"

definition simon_64_96_key_size :: nat where
  "simon_64_96_key_size = 96"

definition simon_64_96_rounds :: nat where
  "simon_64_96_rounds = 42"

definition simon_64_96_key_words :: nat where
  "simon_64_96_key_words = 3"

definition simon_64_96_word_mask :: "32 word" where
  "simon_64_96_word_mask = (-1)"

definition simon_64_96_round_constant :: "32 word" where
  "simon_64_96_round_constant = 0xFFFFFFFC"

definition simon_64_96_z_sequence :: int where
  "simon_64_96_z_sequence = 0x3369F885192C0EF5"





definition simon_64_96_rol :: "32 word \<Rightarrow> nat \<Rightarrow> 32 word" where
  "simon_64_96_rol x r = word_rotl r x"

definition simon_64_96_ror :: "32 word \<Rightarrow> nat \<Rightarrow> 32 word" where
  "simon_64_96_ror x r = word_rotr r x"

definition simon_64_96_f :: "32 word \<Rightarrow> 32 word" where
  "simon_64_96_f x =
     (let s1 = simon_64_96_rol x 1;
          s8 = simon_64_96_rol x 8;
          s2 = simon_64_96_rol x 2
      in xor (and s1 s8) s2)"

definition simon_64_96_encrypt_round ::
  "32 word \<Rightarrow> (32 word \<times> 32 word) \<Rightarrow> (32 word \<times> 32 word)" where
  "simon_64_96_encrypt_round k xy =
     (let x = fst xy;
          y = snd xy;
          fx = simon_64_96_f x;
          new_x = xor (xor y fx) k;
          new_y = x
      in (new_x, new_y))"

definition simon_64_96_decrypt_round ::
  "32 word \<Rightarrow> (32 word \<times> 32 word) \<Rightarrow> (32 word \<times> 32 word)" where
  "simon_64_96_decrypt_round k xy =
     (let x = fst xy;
          y = snd xy;
          fy = simon_64_96_f y;
          new_x = y;
          new_y = xor (xor x fy) k
      in (new_x, new_y))"





definition simon_64_96_key_to_words ::
  "96 word \<Rightarrow> (32 word \<times> 32 word \<times> 32 word)" where
  "simon_64_96_key_to_words master_key =
     (let           k0 = ucast master_key;
          k1 = ucast (drop_bit 32 master_key);
          k2 = ucast (drop_bit 64 master_key)
      in (k0, k1, k2))"


function simon_64_96_generate_round_keys_rec ::
  "32 word list \<Rightarrow> int \<Rightarrow> nat \<Rightarrow> 32 word list" where
  "simon_64_96_generate_round_keys_rec rk z i =
     (if i \<ge> simon_64_96_rounds then rk
      else
        let rk_im3 = rk ! (i - 3);
            rk_im1 = rk ! (i - 1);
            rs_3 = simon_64_96_ror rk_im1 3;
            rs_4 = simon_64_96_ror rk_im1 4;
            tmp = xor rk_im3 (xor rs_3 rs_4);
            const_bit = (if bit z 0 then (1 :: 32 word) else 0);
            new_k = xor simon_64_96_round_constant (xor const_bit tmp);
            z_next = (z div 2) + (z mod 2) * (2 ^ 61)
        in simon_64_96_generate_round_keys_rec (rk @ [new_k]) z_next (i + 1))"
  by pat_completeness auto

termination simon_64_96_generate_round_keys_rec
  apply (relation "measure (\<lambda>(rk, z, i). simon_64_96_rounds - i)")
  apply (auto simp: simon_64_96_rounds_def)
  done


definition simon_64_96_generate_round_keys :: "96 word \<Rightarrow> 32 word list" where
  "simon_64_96_generate_round_keys master_key =
     (let (k0, k1, k2) = simon_64_96_key_to_words master_key;
          rk0 = [k0, k1, k2]
      in simon_64_96_generate_round_keys_rec rk0 simon_64_96_z_sequence 3)"




definition simon_64_96_block_to_words :: "64 word \<Rightarrow> (32 word \<times> 32 word)" where
  "simon_64_96_block_to_words block =
     (let left = ucast (drop_bit 32 block);
          right = ucast block
      in (left, right))"

definition simon_64_96_words_to_block :: "32 word \<Rightarrow> 32 word \<Rightarrow> 64 word" where
  "simon_64_96_words_to_block left right =
     or (push_bit 32 (ucast left)) (ucast right)"

fun simon_64_96_encrypt_block_iter ::
  "(32 word \<times> 32 word) \<Rightarrow> 32 word list \<Rightarrow> (32 word \<times> 32 word)" where
  "simon_64_96_encrypt_block_iter state [] = state"
| "simon_64_96_encrypt_block_iter state (k # ks) =
     simon_64_96_encrypt_block_iter (simon_64_96_encrypt_round k state) ks"

definition simon_64_96_encrypt_block ::
  "64 word \<Rightarrow> 32 word list \<Rightarrow> 64 word" where
  "simon_64_96_encrypt_block plaintext round_keys =
     (let state = simon_64_96_block_to_words plaintext;
          final_state = simon_64_96_encrypt_block_iter state round_keys;
          left = fst final_state;
          right = snd final_state
      in simon_64_96_words_to_block left right)"

definition simon_64_96_decrypt_block ::
  "64 word \<Rightarrow> 32 word list \<Rightarrow> 64 word" where
  "simon_64_96_decrypt_block ciphertext round_keys =
     (let state = simon_64_96_block_to_words ciphertext;
          final_state = foldl (\<lambda>st k. simon_64_96_decrypt_round k st) state (rev round_keys);
          left = fst final_state;
          right = snd final_state
      in simon_64_96_words_to_block left right)"

definition simon_64_96_encrypt :: "64 word \<Rightarrow> 96 word \<Rightarrow> 64 word" where
  "simon_64_96_encrypt plaintext master_key =
     (let round_keys = simon_64_96_generate_round_keys master_key
      in simon_64_96_encrypt_block plaintext round_keys)"

definition simon_64_96_decrypt :: "64 word \<Rightarrow> 96 word \<Rightarrow> 64 word" where
  "simon_64_96_decrypt ciphertext master_key =
     (let round_keys = simon_64_96_generate_round_keys master_key
      in simon_64_96_decrypt_block ciphertext round_keys)"




definition simon_64_96_test_plaintext :: "64 word" where
  "simon_64_96_test_plaintext =
     simon_64_96_words_to_block 0x6F722067 0x6E696C63"

definition simon_64_96_test_key :: "96 word" where
  "simon_64_96_test_key =
     (push_bit 64 (ucast (0x13121110 :: 32 word)))
          + (push_bit 32 (ucast (0x0B0A0908 :: 32 word)))
          + 0x03020100"

definition simon_64_96_test_ciphertext :: "64 word" where
  "simon_64_96_test_ciphertext =
     simon_64_96_words_to_block 0x5CA2E27F 0x111A8FC8"


lemma simon_64_96_test_vector_encrypt_correct:
  "simon_64_96_encrypt simon_64_96_test_plaintext simon_64_96_test_key
   = simon_64_96_test_ciphertext"
  by eval

lemma simon_64_96_test_vector_decrypt_correct:
  "simon_64_96_decrypt simon_64_96_test_ciphertext simon_64_96_test_key
   = simon_64_96_test_plaintext"
  by eval

end
