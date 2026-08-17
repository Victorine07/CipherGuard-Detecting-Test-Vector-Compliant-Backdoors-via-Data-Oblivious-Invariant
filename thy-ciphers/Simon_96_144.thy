theory Simon_96_144
  imports
    "HOL-Library.Word"
    "HOL.Bit_Operations"
begin




definition simon_96_144_word_size :: nat where
  "simon_96_144_word_size = 48"

definition simon_96_144_block_size :: nat where
  "simon_96_144_block_size = 96"

definition simon_96_144_key_size :: nat where
  "simon_96_144_key_size = 144"

definition simon_96_144_rounds :: nat where
  "simon_96_144_rounds = 54"

definition simon_96_144_key_words :: nat where
  "simon_96_144_key_words = 3"

definition simon_96_144_word_mask :: "48 word" where
  "simon_96_144_word_mask = (-1)"

definition simon_96_144_round_constant :: "48 word" where
  "simon_96_144_round_constant = 0xFFFFFFFFFFFC"

definition simon_96_144_z_sequence :: int where
  "simon_96_144_z_sequence = 0x3C2CE51207A635DB"





definition simon_96_144_rol :: "48 word \<Rightarrow> nat \<Rightarrow> 48 word" where
  "simon_96_144_rol x r = word_rotl r x"

definition simon_96_144_ror :: "48 word \<Rightarrow> nat \<Rightarrow> 48 word" where
  "simon_96_144_ror x r = word_rotr r x"

definition simon_96_144_f :: "48 word \<Rightarrow> 48 word" where
  "simon_96_144_f x =
     (let s1 = simon_96_144_rol x 1;
          s8 = simon_96_144_rol x 8;
          s2 = simon_96_144_rol x 2
      in xor (and s1 s8) s2)"

definition simon_96_144_encrypt_round ::
  "48 word \<Rightarrow> (48 word \<times> 48 word) \<Rightarrow> (48 word \<times> 48 word)" where
  "simon_96_144_encrypt_round k xy =
     (let x = fst xy;
          y = snd xy;
          fx = simon_96_144_f x;
          new_x = xor (xor y fx) k;
          new_y = x
      in (new_x, new_y))"

definition simon_96_144_decrypt_round ::
  "48 word \<Rightarrow> (48 word \<times> 48 word) \<Rightarrow> (48 word \<times> 48 word)" where
  "simon_96_144_decrypt_round k xy =
     (let x = fst xy;
          y = snd xy;
          fy = simon_96_144_f y;
          new_x = y;
          new_y = xor (xor x fy) k
      in (new_x, new_y))"





definition simon_96_144_key_to_words ::
  "144 word \<Rightarrow> (48 word \<times> 48 word \<times> 48 word)" where
  "simon_96_144_key_to_words master_key =
     (let           k0 = ucast master_key;
          k1 = ucast (drop_bit 48 master_key);
          k2 = ucast (drop_bit 96 master_key)
      in (k0, k1, k2))"


function simon_96_144_generate_round_keys_rec ::
  "48 word list \<Rightarrow> int \<Rightarrow> nat \<Rightarrow> 48 word list" where
  "simon_96_144_generate_round_keys_rec rk z i =
     (if i \<ge> simon_96_144_rounds then rk
      else
        let rk_im3 = rk ! (i - 3);
            rk_im1 = rk ! (i - 1);
            rs_3 = simon_96_144_ror rk_im1 3;
            rs_4 = simon_96_144_ror rk_im1 4;
            tmp = xor rk_im3 (xor rs_3 rs_4);
            const_bit = (if bit z 0 then (1 :: 48 word) else 0);
            new_k = xor simon_96_144_round_constant (xor const_bit tmp);
            z_next = (z div 2) + (z mod 2) * (2 ^ 61)
        in simon_96_144_generate_round_keys_rec (rk @ [new_k]) z_next (i + 1))"
  by pat_completeness auto

termination simon_96_144_generate_round_keys_rec
  apply (relation "measure (\<lambda>(rk, z, i). simon_96_144_rounds - i)")
  apply (auto simp: simon_96_144_rounds_def)
  done


definition simon_96_144_generate_round_keys :: "144 word \<Rightarrow> 48 word list" where
  "simon_96_144_generate_round_keys master_key =
     (let (k0, k1, k2) = simon_96_144_key_to_words master_key;
          rk0 = [k0, k1, k2]
      in simon_96_144_generate_round_keys_rec rk0 simon_96_144_z_sequence 3)"




definition simon_96_144_block_to_words :: "96 word \<Rightarrow> (48 word \<times> 48 word)" where
  "simon_96_144_block_to_words block =
     (let left = ucast (drop_bit 48 block);
          right = ucast block
      in (left, right))"

definition simon_96_144_words_to_block :: "48 word \<Rightarrow> 48 word \<Rightarrow> 96 word" where
  "simon_96_144_words_to_block left right =
     or (push_bit 48 (ucast left)) (ucast right)"

fun simon_96_144_encrypt_block_iter ::
  "(48 word \<times> 48 word) \<Rightarrow> 48 word list \<Rightarrow> (48 word \<times> 48 word)" where
  "simon_96_144_encrypt_block_iter state [] = state"
| "simon_96_144_encrypt_block_iter state (k # ks) =
     simon_96_144_encrypt_block_iter (simon_96_144_encrypt_round k state) ks"

definition simon_96_144_encrypt_block ::
  "96 word \<Rightarrow> 48 word list \<Rightarrow> 96 word" where
  "simon_96_144_encrypt_block plaintext round_keys =
     (let state = simon_96_144_block_to_words plaintext;
          final_state = simon_96_144_encrypt_block_iter state round_keys;
          left = fst final_state;
          right = snd final_state
      in simon_96_144_words_to_block left right)"

definition simon_96_144_decrypt_block ::
  "96 word \<Rightarrow> 48 word list \<Rightarrow> 96 word" where
  "simon_96_144_decrypt_block ciphertext round_keys =
     (let state = simon_96_144_block_to_words ciphertext;
          final_state = foldl (\<lambda>st k. simon_96_144_decrypt_round k st) state (rev round_keys);
          left = fst final_state;
          right = snd final_state
      in simon_96_144_words_to_block left right)"

definition simon_96_144_encrypt :: "96 word \<Rightarrow> 144 word \<Rightarrow> 96 word" where
  "simon_96_144_encrypt plaintext master_key =
     (let round_keys = simon_96_144_generate_round_keys master_key
      in simon_96_144_encrypt_block plaintext round_keys)"

definition simon_96_144_decrypt :: "96 word \<Rightarrow> 144 word \<Rightarrow> 96 word" where
  "simon_96_144_decrypt ciphertext master_key =
     (let round_keys = simon_96_144_generate_round_keys master_key
      in simon_96_144_decrypt_block ciphertext round_keys)"




definition simon_96_144_test_plaintext :: "96 word" where
  "simon_96_144_test_plaintext =
     simon_96_144_words_to_block 0x6461657220747369 0x20656874206E6920"

definition simon_96_144_test_key :: "144 word" where
  "simon_96_144_test_key =
     (push_bit 96 (ucast (0x131211100F0E0D0C :: 48 word)))
          + (push_bit 48 (ucast (0x0B0A090807060504 :: 48 word)))
          + 0x03020100"

(* No official ciphertext test vector was available when this theory was
   authored (mirrors python ciphers/simon_96_144.py, which marks its own
   ciphertext as "verification pending official vector" and checks
   correctness via round-trip self-consistency instead). A
   simon_96_144_test_ciphertext constant is intentionally omitted rather
   than filled with a fabricated value. *)

end
