theory Simon_48_72
  imports
    "HOL-Library.Word"
    "HOL.Bit_Operations"
begin




definition simon_48_72_word_size :: nat where
  "simon_48_72_word_size = 24"

definition simon_48_72_block_size :: nat where
  "simon_48_72_block_size = 48"

definition simon_48_72_key_size :: nat where
  "simon_48_72_key_size = 72"

definition simon_48_72_rounds :: nat where
  "simon_48_72_rounds = 36"

definition simon_48_72_key_words :: nat where
  "simon_48_72_key_words = 3"

definition simon_48_72_word_mask :: "24 word" where
  "simon_48_72_word_mask = (-1)"

definition simon_48_72_round_constant :: "24 word" where
  "simon_48_72_round_constant = 0xFFFFFC"

definition simon_48_72_z_sequence :: int where
  "simon_48_72_z_sequence = 0x19C3522FB386A45F"





definition simon_48_72_rol :: "24 word \<Rightarrow> nat \<Rightarrow> 24 word" where
  "simon_48_72_rol x r = word_rotl r x"

definition simon_48_72_ror :: "24 word \<Rightarrow> nat \<Rightarrow> 24 word" where
  "simon_48_72_ror x r = word_rotr r x"

definition simon_48_72_f :: "24 word \<Rightarrow> 24 word" where
  "simon_48_72_f x =
     (let s1 = simon_48_72_rol x 1;
          s8 = simon_48_72_rol x 8;
          s2 = simon_48_72_rol x 2
      in xor (and s1 s8) s2)"

definition simon_48_72_encrypt_round ::
  "24 word \<Rightarrow> (24 word \<times> 24 word) \<Rightarrow> (24 word \<times> 24 word)" where
  "simon_48_72_encrypt_round k xy =
     (let x = fst xy;
          y = snd xy;
          fx = simon_48_72_f x;
          new_x = xor (xor y fx) k;
          new_y = x
      in (new_x, new_y))"

definition simon_48_72_decrypt_round ::
  "24 word \<Rightarrow> (24 word \<times> 24 word) \<Rightarrow> (24 word \<times> 24 word)" where
  "simon_48_72_decrypt_round k xy =
     (let x = fst xy;
          y = snd xy;
          fy = simon_48_72_f y;
          new_x = y;
          new_y = xor (xor x fy) k
      in (new_x, new_y))"





definition simon_48_72_key_to_words ::
  "72 word \<Rightarrow> (24 word \<times> 24 word \<times> 24 word)" where
  "simon_48_72_key_to_words master_key =
     (let           k0 = ucast master_key;
          k1 = ucast (drop_bit 24 master_key);
          k2 = ucast (drop_bit 48 master_key)
      in (k0, k1, k2))"


function simon_48_72_generate_round_keys_rec ::
  "24 word list \<Rightarrow> int \<Rightarrow> nat \<Rightarrow> 24 word list" where
  "simon_48_72_generate_round_keys_rec rk z i =
     (if i \<ge> simon_48_72_rounds then rk
      else
        let rk_im3 = rk ! (i - 3);
            rk_im1 = rk ! (i - 1);
            rs_3 = simon_48_72_ror rk_im1 3;
            rs_4 = simon_48_72_ror rk_im1 4;
            tmp = xor rk_im3 (xor rs_3 rs_4);
            const_bit = (if bit z 0 then (1 :: 24 word) else 0);
            new_k = xor simon_48_72_round_constant (xor const_bit tmp);
            z_next = (z div 2) + (z mod 2) * (2 ^ 61)
        in simon_48_72_generate_round_keys_rec (rk @ [new_k]) z_next (i + 1))"
  by pat_completeness auto

termination simon_48_72_generate_round_keys_rec
  apply (relation "measure (\<lambda>(rk, z, i). simon_48_72_rounds - i)")
  apply (auto simp: simon_48_72_rounds_def)
  done


definition simon_48_72_generate_round_keys :: "72 word \<Rightarrow> 24 word list" where
  "simon_48_72_generate_round_keys master_key =
     (let (k0, k1, k2) = simon_48_72_key_to_words master_key;
          rk0 = [k0, k1, k2]
      in simon_48_72_generate_round_keys_rec rk0 simon_48_72_z_sequence 3)"




definition simon_48_72_block_to_words :: "48 word \<Rightarrow> (24 word \<times> 24 word)" where
  "simon_48_72_block_to_words block =
     (let left = ucast (drop_bit 24 block);
          right = ucast block
      in (left, right))"

definition simon_48_72_words_to_block :: "24 word \<Rightarrow> 24 word \<Rightarrow> 48 word" where
  "simon_48_72_words_to_block left right =
     or (push_bit 24 (ucast left)) (ucast right)"

fun simon_48_72_encrypt_block_iter ::
  "(24 word \<times> 24 word) \<Rightarrow> 24 word list \<Rightarrow> (24 word \<times> 24 word)" where
  "simon_48_72_encrypt_block_iter state [] = state"
| "simon_48_72_encrypt_block_iter state (k # ks) =
     simon_48_72_encrypt_block_iter (simon_48_72_encrypt_round k state) ks"

definition simon_48_72_encrypt_block ::
  "48 word \<Rightarrow> 24 word list \<Rightarrow> 48 word" where
  "simon_48_72_encrypt_block plaintext round_keys =
     (let state = simon_48_72_block_to_words plaintext;
          final_state = simon_48_72_encrypt_block_iter state round_keys;
          left = fst final_state;
          right = snd final_state
      in simon_48_72_words_to_block left right)"

definition simon_48_72_decrypt_block ::
  "48 word \<Rightarrow> 24 word list \<Rightarrow> 48 word" where
  "simon_48_72_decrypt_block ciphertext round_keys =
     (let state = simon_48_72_block_to_words ciphertext;
          final_state = foldl (\<lambda>st k. simon_48_72_decrypt_round k st) state (rev round_keys);
          left = fst final_state;
          right = snd final_state
      in simon_48_72_words_to_block left right)"

definition simon_48_72_encrypt :: "48 word \<Rightarrow> 72 word \<Rightarrow> 48 word" where
  "simon_48_72_encrypt plaintext master_key =
     (let round_keys = simon_48_72_generate_round_keys master_key
      in simon_48_72_encrypt_block plaintext round_keys)"

definition simon_48_72_decrypt :: "48 word \<Rightarrow> 72 word \<Rightarrow> 48 word" where
  "simon_48_72_decrypt ciphertext master_key =
     (let round_keys = simon_48_72_generate_round_keys master_key
      in simon_48_72_decrypt_block ciphertext round_keys)"




text \<open>Official SIMON-48/72 test vector (the previous version of this
  constant set mistakenly used SIMON-48/96's vector, which has a
  different, 4-word key not valid for this 3-word-key variant).\<close>

definition simon_48_72_test_plaintext :: "48 word" where
  "simon_48_72_test_plaintext =
     simon_48_72_words_to_block 0x612067 0x6E696C"

definition simon_48_72_test_key :: "72 word" where
  "simon_48_72_test_key =
     (push_bit 48 (ucast (0x121110 :: 24 word)))
          + (push_bit 24 (ucast (0x0A0908 :: 24 word)))
          + 0x020100"

definition simon_48_72_test_ciphertext :: "48 word" where
  "simon_48_72_test_ciphertext =
     simon_48_72_words_to_block 0xDAE5AC 0x292CAC"


lemma simon_48_72_test_vector_encrypt_correct:
  "simon_48_72_encrypt simon_48_72_test_plaintext simon_48_72_test_key
   = simon_48_72_test_ciphertext"
  by eval

lemma simon_48_72_test_vector_decrypt_correct:
  "simon_48_72_decrypt simon_48_72_test_ciphertext simon_48_72_test_key
   = simon_48_72_test_plaintext"
  by eval

end
