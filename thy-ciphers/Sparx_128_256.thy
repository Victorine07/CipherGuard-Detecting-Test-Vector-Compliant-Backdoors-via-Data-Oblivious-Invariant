theory Sparx_128_256
  imports
    "HOL-Library.Word"
    "HOL.Bit_Operations"
begin

text \<open>
  SPARX-128/256, matching the official CryptoLUX reference implementation
  (Dinu, Perrin, Udovenko, Velichkov, Grossschadl, Biryukov, "Design
  Strategies for ARX-based Symmetric-Key Ciphers", CHES 2016;
  https://github.com/cryptolu/SPARX, ref-c/sparx.c).
\<close>


definition sparx_128_256_block_size :: nat where "sparx_128_256_block_size = 128"


definition sparx_128_256_key_size :: nat where "sparx_128_256_key_size = 256"


definition sparx_128_256_n_steps :: nat where "sparx_128_256_n_steps = 10"


definition sparx_128_256_rounds_per_step :: nat where "sparx_128_256_rounds_per_step = 4"


definition sparx_128_256_word_size :: nat where "sparx_128_256_word_size = 16"


definition sparx_128_256_n_branches :: nat where "sparx_128_256_n_branches = 4"


definition sparx_128_256_n_words :: nat where "sparx_128_256_n_words = 8"


definition sparx_128_256_round_key_words :: nat where
  "sparx_128_256_round_key_words = 2"


definition sparx_128_256_rol :: "'a::len word \<Rightarrow> nat \<Rightarrow> 'a word" where
  "sparx_128_256_rol x r = word_rotl r x"


definition sparx_128_256_ror :: "'a::len word \<Rightarrow> nat \<Rightarrow> 'a word" where
  "sparx_128_256_ror x r = word_rotr r x"


definition sparx_128_256_a_perm :: "16 word \<Rightarrow> 16 word \<Rightarrow> (16 word \<times> 16 word)" where
  "sparx_128_256_a_perm l r = (
    let l1 = sparx_128_256_rol l 9;
        l2 = l1 + r;
        r1 = sparx_128_256_rol r 2;
        r2 = xor r1 l2
    in (l2, r2))"


definition sparx_128_256_a_perm_inv :: "16 word \<Rightarrow> 16 word \<Rightarrow> (16 word \<times> 16 word)" where
  "sparx_128_256_a_perm_inv l r = (
    let r1 = xor r l;
        r2 = sparx_128_256_rol r1 14;
        l1 = l - r2;
        l2 = sparx_128_256_rol l1 7
    in (l2, r2))"


definition sparx_128_256_l_w :: "16 word \<Rightarrow> 16 word" where
  "sparx_128_256_l_w x = sparx_128_256_rol x 8"


definition sparx_128_256_linear_layer :: "16 word list \<Rightarrow> 16 word list" where
  "sparx_128_256_linear_layer s = (
    let x0 = s ! 0; x1 = s ! 1; x2 = s ! 2; x3 = s ! 3;
        t = sparx_128_256_l_w (xor x0 (xor x1 (xor x2 x3)))
    in [xor (s ! 4) (xor x2 t), xor (s ! 5) (xor x1 t),
        xor (s ! 6) (xor x0 t), xor (s ! 7) (xor x3 t),
        x0, x1, x2, x3])"


definition sparx_128_256_linear_layer_inv :: "16 word list \<Rightarrow> 16 word list" where
  "sparx_128_256_linear_layer_inv s = (
    let y0 = s ! 0; y1 = s ! 1; y2 = s ! 2; y3 = s ! 3;
        x0 = s ! 4; x1 = s ! 5; x2 = s ! 6; x3 = s ! 7;
        t = sparx_128_256_l_w (xor x0 (xor x1 (xor x2 x3)))
    in [x0, x1, x2, x3,
        xor y0 (xor x2 t), xor y1 (xor x1 t),
        xor y2 (xor x0 t), xor y3 (xor x3 t)])"


definition sparx_128_256_apply_encrypt_round ::
  "16 word \<Rightarrow> 16 word \<Rightarrow> 16 word \<Rightarrow> 16 word \<Rightarrow> (16 word \<times> 16 word)" where
  "sparx_128_256_apply_encrypt_round x0 x1 key1 key2 = (
    let x0' = xor x0 key1;
        x1' = xor x1 key2
    in sparx_128_256_a_perm x0' x1')"


definition sparx_128_256_apply_decrypt_round ::
  "16 word \<Rightarrow> 16 word \<Rightarrow> 16 word \<Rightarrow> 16 word \<Rightarrow> (16 word \<times> 16 word)" where
  "sparx_128_256_apply_decrypt_round x0 x1 key1 key2 = (
    let (x0', x1') = sparx_128_256_a_perm_inv x0 x1
    in (xor x0' key1, xor x1' key2))"


definition sparx_128_256_extract_key_words :: "256 word \<Rightarrow> 16 word list" where
  "sparx_128_256_extract_key_words master_key =
    [ucast master_key,
     ucast (drop_bit 16 master_key),
     ucast (drop_bit 32 master_key),
     ucast (drop_bit 48 master_key),
     ucast (drop_bit 64 master_key),
     ucast (drop_bit 80 master_key),
     ucast (drop_bit 96 master_key),
     ucast (drop_bit 112 master_key),
     ucast (drop_bit 128 master_key),
     ucast (drop_bit 144 master_key),
     ucast (drop_bit 160 master_key),
     ucast (drop_bit 176 master_key),
     ucast (drop_bit 192 master_key),
     ucast (drop_bit 208 master_key),
     ucast (drop_bit 224 master_key),
     ucast (drop_bit 240 master_key)]"


definition sparx_128_256_k_perm :: "16 word list \<Rightarrow> nat \<Rightarrow> 16 word list" where
  "sparx_128_256_k_perm k c = (
    let (k0, k1) = sparx_128_256_a_perm (k ! 0) (k ! 1);
        k2 = (k ! 2) + k0;
        k3 = (k ! 3) + k1;
        (k8, k9) = sparx_128_256_a_perm (k ! 8) (k ! 9);
        k10 = (k ! 10) + k8;
        k11 = (k ! 11) + k9 + (word_of_nat c);
        k_first10 = [k0, k1, k2, k3, k ! 4, k ! 5, k ! 6, k ! 7, k8, k9]
    in [k10, k11, k ! 12, k ! 13, k ! 14, k ! 15] @ k_first10)"


function sparx_128_256_gen_key_schedule_iterate ::
  "16 word list \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> 16 word list list \<Rightarrow> 16 word list list" where
  "sparx_128_256_gen_key_schedule_iterate k c max_c acc = (
    if c \<ge> max_c then acc
    else
      let row = take (2 * sparx_128_256_rounds_per_step) k;
          k' = sparx_128_256_k_perm k (c + 1)
      in sparx_128_256_gen_key_schedule_iterate k' (c + 1) max_c (acc @ [row]))"
  by pat_completeness auto
termination
  by (relation "measure (\<lambda>(k, c, max_c, acc). max_c - c)") auto


definition sparx_128_256_generate_key_schedule :: "256 word \<Rightarrow> 16 word list list" where
  "sparx_128_256_generate_key_schedule master_key = (
    let k = sparx_128_256_extract_key_words master_key;
        max_c = sparx_128_256_n_branches * sparx_128_256_n_steps + 1
    in sparx_128_256_gen_key_schedule_iterate k 0 max_c [])"


definition sparx_128_256_block_to_words :: "128 word \<Rightarrow> 16 word list" where
  "sparx_128_256_block_to_words block =
    [ucast block,
     ucast (drop_bit 16 block),
     ucast (drop_bit 32 block),
     ucast (drop_bit 48 block),
     ucast (drop_bit 64 block),
     ucast (drop_bit 80 block),
     ucast (drop_bit 96 block),
     ucast (drop_bit 112 block)]"


definition sparx_128_256_words_to_block :: "16 word list \<Rightarrow> 128 word" where
  "sparx_128_256_words_to_block words =
    or (push_bit 112 (ucast (words ! 7)))
    (or (push_bit 96 (ucast (words ! 6)))
    (or (push_bit 80 (ucast (words ! 5)))
    (or (push_bit 64 (ucast (words ! 4)))
    (or (push_bit 48 (ucast (words ! 3)))
    (or (push_bit 32 (ucast (words ! 2)))
    (or (push_bit 16 (ucast (words ! 1)))
        (ucast (words ! 0))))))))"


function sparx_128_256_encrypt_round_iterate ::
  "16 word \<Rightarrow> 16 word \<Rightarrow> 16 word list list \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> (16 word \<times> 16 word)" where
  "sparx_128_256_encrypt_round_iterate x0 x1 all_keys row r = (
    if r \<ge> sparx_128_256_rounds_per_step then (x0, x1)
    else
      let key1 = (all_keys ! row) ! (2 * r);
          key2 = (all_keys ! row) ! (2 * r + 1);
          (x0', x1') = sparx_128_256_apply_encrypt_round x0 x1 key1 key2
      in sparx_128_256_encrypt_round_iterate x0' x1' all_keys row (r + 1))"
  by pat_completeness auto
termination
  by (relation "measure (\<lambda>(x0, x1, all_keys, row, r). sparx_128_256_rounds_per_step - r)") auto


function sparx_128_256_decrypt_round_iterate ::
  "16 word \<Rightarrow> 16 word \<Rightarrow> 16 word list list \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> (16 word \<times> 16 word)" where
  "sparx_128_256_decrypt_round_iterate x0 x1 all_keys row r = (
    if r > sparx_128_256_rounds_per_step then (x0, x1)
    else
      let key1 = (all_keys ! row) ! (2 * r);
          key2 = (all_keys ! row) ! (2 * r + 1);
          (x0', x1') = sparx_128_256_apply_decrypt_round x0 x1 key1 key2
      in if r = 0 then (x0', x1')
         else sparx_128_256_decrypt_round_iterate x0' x1' all_keys row (r - 1))"
  by pat_completeness auto
termination
  by (relation "measure (\<lambda>(x0, x1, all_keys, row, r). r)") auto


definition sparx_128_256_encrypt_step_iterate ::
  "16 word list \<Rightarrow> 16 word list list \<Rightarrow> nat \<Rightarrow> 16 word list" where
  "sparx_128_256_encrypt_step_iterate state all_keys step = (
    let row0 = sparx_128_256_n_branches * step;
        (s0, s1) = sparx_128_256_encrypt_round_iterate (state ! 0) (state ! 1) all_keys row0 0;
        (s2, s3) = sparx_128_256_encrypt_round_iterate (state ! 2) (state ! 3) all_keys (row0 + 1) 0;
        (s4, s5) = sparx_128_256_encrypt_round_iterate (state ! 4) (state ! 5) all_keys (row0 + 2) 0;
        (s6, s7) = sparx_128_256_encrypt_round_iterate (state ! 6) (state ! 7) all_keys (row0 + 3) 0
    in [s0, s1, s2, s3, s4, s5, s6, s7])"


definition sparx_128_256_decrypt_step_iterate ::
  "16 word list \<Rightarrow> 16 word list list \<Rightarrow> nat \<Rightarrow> 16 word list" where
  "sparx_128_256_decrypt_step_iterate state all_keys step = (
    let row0 = sparx_128_256_n_branches * step;
        (s0, s1) = sparx_128_256_decrypt_round_iterate (state ! 0) (state ! 1) all_keys row0
                     (sparx_128_256_rounds_per_step - 1);
        (s2, s3) = sparx_128_256_decrypt_round_iterate (state ! 2) (state ! 3) all_keys (row0 + 1)
                     (sparx_128_256_rounds_per_step - 1);
        (s4, s5) = sparx_128_256_decrypt_round_iterate (state ! 4) (state ! 5) all_keys (row0 + 2)
                     (sparx_128_256_rounds_per_step - 1);
        (s6, s7) = sparx_128_256_decrypt_round_iterate (state ! 6) (state ! 7) all_keys (row0 + 3)
                     (sparx_128_256_rounds_per_step - 1)
    in [s0, s1, s2, s3, s4, s5, s6, s7])"


function sparx_128_256_encrypt_steps_iterate ::
  "16 word list \<Rightarrow> 16 word list list \<Rightarrow> nat \<Rightarrow> 16 word list" where
  "sparx_128_256_encrypt_steps_iterate state all_keys step = (
    if step \<ge> sparx_128_256_n_steps then state
    else
      let state' = sparx_128_256_encrypt_step_iterate state all_keys step;
          state'' = sparx_128_256_linear_layer state'
      in sparx_128_256_encrypt_steps_iterate state'' all_keys (step + 1))"
  by pat_completeness auto
termination
  by (relation "measure (\<lambda>(state, all_keys, step). sparx_128_256_n_steps - step)") auto


function sparx_128_256_decrypt_steps_iterate ::
  "16 word list \<Rightarrow> 16 word list list \<Rightarrow> nat \<Rightarrow> 16 word list" where
  "sparx_128_256_decrypt_steps_iterate state all_keys step = (
    let state' = sparx_128_256_linear_layer_inv state;
        state'' = sparx_128_256_decrypt_step_iterate state' all_keys step
    in if step = 0 then state''
       else sparx_128_256_decrypt_steps_iterate state'' all_keys (step - 1))"
  by pat_completeness auto
termination
  by (relation "measure (\<lambda>(state, all_keys, step). step)") auto


definition sparx_128_256_encrypt_block ::
  "128 word \<Rightarrow> 16 word list list \<Rightarrow> 128 word" where
  "sparx_128_256_encrypt_block plaintext all_keys = (
    let state = sparx_128_256_block_to_words plaintext;
        state' = sparx_128_256_encrypt_steps_iterate state all_keys 0;
        whitening_row = sparx_128_256_n_branches * sparx_128_256_n_steps;
        wk = all_keys ! whitening_row;
        state_final = [xor (state' ! 0) (wk ! 0), xor (state' ! 1) (wk ! 1),
                        xor (state' ! 2) (wk ! 2), xor (state' ! 3) (wk ! 3),
                        xor (state' ! 4) (wk ! 4), xor (state' ! 5) (wk ! 5),
                        xor (state' ! 6) (wk ! 6), xor (state' ! 7) (wk ! 7)]
    in sparx_128_256_words_to_block state_final)"


definition sparx_128_256_decrypt_block ::
  "128 word \<Rightarrow> 16 word list list \<Rightarrow> 128 word" where
  "sparx_128_256_decrypt_block ciphertext all_keys = (
    let state = sparx_128_256_block_to_words ciphertext;
        whitening_row = sparx_128_256_n_branches * sparx_128_256_n_steps;
        wk = all_keys ! whitening_row;
        state_unwhitened = [xor (state ! 0) (wk ! 0), xor (state ! 1) (wk ! 1),
                             xor (state ! 2) (wk ! 2), xor (state ! 3) (wk ! 3),
                             xor (state ! 4) (wk ! 4), xor (state ! 5) (wk ! 5),
                             xor (state ! 6) (wk ! 6), xor (state ! 7) (wk ! 7)];
        state' = sparx_128_256_decrypt_steps_iterate state_unwhitened all_keys (sparx_128_256_n_steps - 1)
    in sparx_128_256_words_to_block state')"


definition sparx_128_256_encrypt :: "128 word \<Rightarrow> 256 word \<Rightarrow> 128 word" where
  "sparx_128_256_encrypt plaintext master_key = (
    let all_keys = sparx_128_256_generate_key_schedule master_key
    in sparx_128_256_encrypt_block plaintext all_keys)"


definition sparx_128_256_decrypt :: "128 word \<Rightarrow> 256 word \<Rightarrow> 128 word" where
  "sparx_128_256_decrypt ciphertext master_key = (
    let all_keys = sparx_128_256_generate_key_schedule master_key
    in sparx_128_256_decrypt_block ciphertext all_keys)"


text \<open>Official test vector (CryptoLUX reference implementation,
  https://github.com/cryptolu/SPARX, ref-c/sparx.c).\<close>

definition sparx_128_256_test_key :: "256 word" where
  "sparx_128_256_test_key =
   0x11003322554477669988bbaaddccffeeeeffccddaabb88996677445522330011"

definition sparx_128_256_test_plaintext :: "128 word" where
  "sparx_128_256_test_plaintext = 0x32107654ba98fedccdef89ab45670123"

definition sparx_128_256_test_ciphertext :: "128 word" where
  "sparx_128_256_test_ciphertext = 0xc820e4b05a5432d16ce614c7e6373328"

lemma sparx_128_256_test_vector_encrypt_correct:
  "sparx_128_256_encrypt sparx_128_256_test_plaintext sparx_128_256_test_key
   = sparx_128_256_test_ciphertext"
  by eval

lemma sparx_128_256_test_vector_decrypt_correct:
  "sparx_128_256_decrypt sparx_128_256_test_ciphertext sparx_128_256_test_key
   = sparx_128_256_test_plaintext"
  by eval

end
