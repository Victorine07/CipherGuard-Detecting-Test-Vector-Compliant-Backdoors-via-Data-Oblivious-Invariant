theory Ascon_64_128
  imports
    "HOL-Library.Word"
    "HOL.Bit_Operations"
begin

section \<open>ASCON-64/128 (Ascon-128): Tiered Core Definitions\<close>

subsection \<open>T1: Constants\<close>

definition ascon_64_128_key_size :: nat where
  "ascon_64_128_key_size = 128"

definition ascon_64_128_nonce_size :: nat where
  "ascon_64_128_nonce_size = 128"

definition ascon_64_128_rate :: nat where
  "ascon_64_128_rate = 64"

definition ascon_64_128_rounds_a :: nat where
  "ascon_64_128_rounds_a = 12"

definition ascon_64_128_rounds_b :: nat where
  "ascon_64_128_rounds_b = 6"


subsection \<open>T2: Primitives\<close>

definition ascon_64_128_add_round_constant :: "64 word list \<Rightarrow> nat \<Rightarrow> 64 word list" where
  "ascon_64_128_add_round_constant state round_index =
     state[2 := xor (state ! 2) (of_nat (240 - 15 * round_index) :: 64 word)]"

definition ascon_64_128_substitution_layer :: "64 word list \<Rightarrow> 64 word list" where
  "ascon_64_128_substitution_layer state =
     (let x0 = state ! 0; x1 = state ! 1; x2 = state ! 2; x3 = state ! 3; x4 = state ! 4;
          a1 = xor x0 x4;
          e1 = xor x4 x3;
          c1 = xor x2 x1;
          t0 = and (not a1) x1;
          t1 = and (not x1) c1;
          t2 = and (not c1) x3;
          t3 = and (not x3) e1;
          t4 = and (not e1) a1;
          a2 = xor a1 t1;
          b2 = xor x1 t2;
          c2 = xor c1 t3;
          d2 = xor x3 t4;
          e2 = xor e1 t0;
          y0 = xor a2 e2;
          y1 = xor b2 a2;
          y2 = not c2;
          y3 = xor d2 c2
      in [y0, y1, y2, y3, e2])"

definition ascon_64_128_linear_diffusion_layer :: "64 word list \<Rightarrow> 64 word list" where
  "ascon_64_128_linear_diffusion_layer state =
     (let x0 = state ! 0; x1 = state ! 1; x2 = state ! 2; x3 = state ! 3; x4 = state ! 4
      in [xor x0 (xor (word_rotr 19 x0) (word_rotr 28 x0)),
          xor x1 (xor (word_rotr 61 x1) (word_rotr 39 x1)),
          xor x2 (xor (word_rotr 1 x2) (word_rotr 6 x2)),
          xor x3 (xor (word_rotr 10 x3) (word_rotr 17 x3)),
          xor x4 (xor (word_rotr 7 x4) (word_rotr 41 x4))])"

definition ascon_64_128_permutation_round :: "64 word list \<Rightarrow> nat \<Rightarrow> 64 word list" where
  "ascon_64_128_permutation_round state round_index =
     ascon_64_128_linear_diffusion_layer
       (ascon_64_128_substitution_layer
         (ascon_64_128_add_round_constant state round_index))"


subsection \<open>T3: Structural Components\<close>

text \<open>ASCON has no key schedule: the key is used directly in initialization and finalization.\<close>


subsection \<open>T4: Orchestration\<close>

function ascon_64_128_permutation_iterate :: "64 word list \<Rightarrow> nat \<Rightarrow> 64 word list" where
  "ascon_64_128_permutation_iterate state round_index =
     (if round_index \<ge> 12 then state
      else ascon_64_128_permutation_iterate
             (ascon_64_128_permutation_round state round_index) (round_index + 1))"
  by pat_completeness auto

termination ascon_64_128_permutation_iterate
  by (relation "measure (\<lambda>(state, round_index). 12 - round_index)") auto

definition ascon_64_128_bytes_to_word :: "8 word list \<Rightarrow> 64 word" where
  "ascon_64_128_bytes_to_word bs = fold (\<lambda>b acc. or (push_bit 8 acc) (ucast b)) bs 0"

definition ascon_64_128_word_to_bytes :: "64 word \<Rightarrow> nat \<Rightarrow> 8 word list" where
  "ascon_64_128_word_to_bytes w n = map (\<lambda>i. ucast (drop_bit (8 * (7 - i)) w) :: 8 word) [0..<n]"

definition ascon_64_128_bytes_to_state :: "8 word list \<Rightarrow> 64 word list" where
  "ascon_64_128_bytes_to_state bs =
     map (\<lambda>w. ascon_64_128_bytes_to_word (take 8 (drop (8 * w) bs))) [0..<5]"

definition ascon_64_128_pad :: "8 word list \<Rightarrow> nat \<Rightarrow> 8 word list" where
  "ascon_64_128_pad data block_bytes =
     data @ [0x80] @ replicate (block_bytes - (length data mod block_bytes) - 1) (0 :: 8 word)"

definition ascon_64_128_initialize :: "8 word list \<Rightarrow> 8 word list \<Rightarrow> 64 word list" where
  "ascon_64_128_initialize key nonce =
     (let iv = [128, 64, 12, 6, 0, 0, 0, 0] :: 8 word list;
          state0 = ascon_64_128_bytes_to_state (iv @ key @ nonce);
          state1 = ascon_64_128_permutation_iterate state0 0;
          zero_key_state =
            ascon_64_128_bytes_to_state (replicate (40 - length key) (0 :: 8 word) @ key)
      in map (\<lambda>i. xor (state1 ! i) (zero_key_state ! i)) [0..<5])"

function ascon_64_128_absorb_ad_blocks :: "64 word list \<Rightarrow> 8 word list \<Rightarrow> 64 word list" where
  "ascon_64_128_absorb_ad_blocks state remaining =
     (if remaining = [] then state
      else
        let w0 = ascon_64_128_bytes_to_word (take 8 remaining);
            state1 = state[0 := xor (state ! 0) w0];
            state2 = ascon_64_128_permutation_iterate state1 (12 - ascon_64_128_rounds_b)
        in ascon_64_128_absorb_ad_blocks state2 (drop 8 remaining))"
  by pat_completeness auto

termination ascon_64_128_absorb_ad_blocks
  by (relation "measure (\<lambda>(state, remaining). length remaining)") auto

definition ascon_64_128_process_associated_data :: "64 word list \<Rightarrow> 8 word list \<Rightarrow> 64 word list" where
  "ascon_64_128_process_associated_data state associated_data =
     (let state1 = (if associated_data = [] then state
                     else ascon_64_128_absorb_ad_blocks state (ascon_64_128_pad associated_data 8))
      in state1[4 := xor (state1 ! 4) 1])"

function ascon_64_128_squeeze_pt_blocks ::
  "64 word list \<Rightarrow> 8 word list \<Rightarrow> nat \<Rightarrow> (64 word list \<times> 8 word list)" where
  "ascon_64_128_squeeze_pt_blocks state remaining p_lastlen =
     (let w0 = ascon_64_128_bytes_to_word (take 8 remaining);
          state1 = state[0 := xor (state ! 0) w0]
      in if length remaining \<le> 8 then
           (state1, take p_lastlen (ascon_64_128_word_to_bytes (state1 ! 0) 8))
         else
           (let (final_state, rest_ct) =
                  ascon_64_128_squeeze_pt_blocks
                    (ascon_64_128_permutation_iterate state1 (12 - ascon_64_128_rounds_b))
                    (drop 8 remaining) p_lastlen
            in (final_state, ascon_64_128_word_to_bytes (state1 ! 0) 8 @ rest_ct)))"
  by pat_completeness auto

termination ascon_64_128_squeeze_pt_blocks
  by (relation "measure (\<lambda>(state, remaining, p_lastlen). length remaining)") auto

definition ascon_64_128_process_plaintext ::
  "64 word list \<Rightarrow> 8 word list \<Rightarrow> (64 word list \<times> 8 word list)" where
  "ascon_64_128_process_plaintext state plaintext =
     (let p_lastlen = length plaintext mod 8;
          padded = ascon_64_128_pad plaintext 8
      in ascon_64_128_squeeze_pt_blocks state padded p_lastlen)"

function ascon_64_128_squeeze_ct_blocks ::
  "64 word list \<Rightarrow> 8 word list \<Rightarrow> nat \<Rightarrow> (64 word list \<times> 8 word list)" where
  "ascon_64_128_squeeze_ct_blocks state remaining c_lastlen =
     (let ci = ascon_64_128_bytes_to_word (take 8 remaining)
      in if length remaining \<le> 8 then
           (let c_padding1 = push_bit ((8 - c_lastlen - 1) * 8) (0x80 :: 64 word);
                c_mask = drop_bit (c_lastlen * 8) (-1 :: 64 word);
                pt_block = take c_lastlen (ascon_64_128_word_to_bytes (xor ci (state ! 0)) 8);
                new0 = xor (xor ci (and (state ! 0) c_mask)) c_padding1
            in (state[0 := new0], pt_block))
         else
           (let pt_block = ascon_64_128_word_to_bytes (xor (state ! 0) ci) 8;
                state1 = state[0 := ci];
                state2 = ascon_64_128_permutation_iterate state1 (12 - ascon_64_128_rounds_b);
                (final_state, rest_pt) =
                  ascon_64_128_squeeze_ct_blocks state2 (drop 8 remaining) c_lastlen
            in (final_state, pt_block @ rest_pt)))"
  by pat_completeness auto

termination ascon_64_128_squeeze_ct_blocks
  by (relation "measure (\<lambda>(state, remaining, c_lastlen). length remaining)") auto

definition ascon_64_128_process_ciphertext ::
  "64 word list \<Rightarrow> 8 word list \<Rightarrow> (64 word list \<times> 8 word list)" where
  "ascon_64_128_process_ciphertext state ciphertext =
     (let c_lastlen = length ciphertext mod 8;
          padded = ciphertext @ replicate (8 - c_lastlen) (0 :: 8 word)
      in ascon_64_128_squeeze_ct_blocks state padded c_lastlen)"

definition ascon_64_128_finalize ::
  "64 word list \<Rightarrow> 8 word list \<Rightarrow> (64 word list \<times> 8 word list)" where
  "ascon_64_128_finalize state key =
     (let k0 = ascon_64_128_bytes_to_word (take 8 key);
          k1 = ascon_64_128_bytes_to_word (take 8 (drop 8 key));
          state1 = state[1 := xor (state ! 1) k0, 2 := xor (state ! 2) k1];
          state2 = ascon_64_128_permutation_iterate state1 0;
          state3 = state2[3 := xor (state2 ! 3) k0, 4 := xor (state2 ! 4) k1];
          tag = ascon_64_128_word_to_bytes (state3 ! 3) 8 @ ascon_64_128_word_to_bytes (state3 ! 4) 8
      in (state3, tag))"

definition ascon_64_128_encrypt ::
  "8 word list \<Rightarrow> 8 word list \<Rightarrow> 8 word list \<Rightarrow> 8 word list \<Rightarrow> 8 word list" where
  "ascon_64_128_encrypt key nonce associated_data plaintext =
     (let state0 = ascon_64_128_initialize key nonce;
          state1 = ascon_64_128_process_associated_data state0 associated_data;
          (state2, ciphertext) = ascon_64_128_process_plaintext state1 plaintext;
          (state3, tag) = ascon_64_128_finalize state2 key
      in ciphertext @ tag)"

definition ascon_64_128_decrypt ::
  "8 word list \<Rightarrow> 8 word list \<Rightarrow> 8 word list \<Rightarrow> 8 word list \<Rightarrow> 8 word list option" where
  "ascon_64_128_decrypt key nonce associated_data ciphertext =
     (let body = take (length ciphertext - 16) ciphertext;
          tag = drop (length ciphertext - 16) ciphertext;
          state0 = ascon_64_128_initialize key nonce;
          state1 = ascon_64_128_process_associated_data state0 associated_data;
          (state2, plaintext) = ascon_64_128_process_ciphertext state1 body;
          (state3, expected_tag) = ascon_64_128_finalize state2 key
      in if expected_tag = tag then Some plaintext else None)"

end
