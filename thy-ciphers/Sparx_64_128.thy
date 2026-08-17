theory Sparx_64_128
  imports
    "HOL-Library.Word"
    "HOL.Bit_Operations"
begin

text \<open>
  SPARX-64/128, matching the official CryptoLUX reference implementation
  (Dinu, Perrin, Udovenko, Velichkov, Grossschadl, Biryukov, "Design
  Strategies for ARX-based Symmetric-Key Ciphers", CHES 2016;
  https://github.com/cryptolu/SPARX, ref-c/sparx.c).
\<close>


definition sparx_64_128_block_size :: nat where "sparx_64_128_block_size = 64"


definition sparx_64_128_key_size :: nat where "sparx_64_128_key_size = 128"


definition sparx_64_128_n_steps :: nat where "sparx_64_128_n_steps = 8"


definition sparx_64_128_rounds_per_step :: nat where "sparx_64_128_rounds_per_step = 3"


definition sparx_64_128_word_size :: nat where "sparx_64_128_word_size = 16"


definition sparx_64_128_n_branches :: nat where "sparx_64_128_n_branches = 2"


definition sparx_64_128_n_words :: nat where "sparx_64_128_n_words = 4"


definition sparx_64_128_round_key_words :: nat where
  "sparx_64_128_round_key_words = 2"


definition sparx_64_128_rol :: "'a::len word \<Rightarrow> nat \<Rightarrow> 'a word" where
  "sparx_64_128_rol x r = word_rotl r x"


definition sparx_64_128_ror :: "'a::len word \<Rightarrow> nat \<Rightarrow> 'a word" where
  "sparx_64_128_ror x r = word_rotr r x"


definition sparx_64_128_a_perm :: "16 word \<Rightarrow> 16 word \<Rightarrow> (16 word \<times> 16 word)" where
  "sparx_64_128_a_perm l r = (
    let l1 = sparx_64_128_rol l 9;
        l2 = l1 + r;
        r1 = sparx_64_128_rol r 2;
        r2 = xor r1 l2
    in (l2, r2))"


definition sparx_64_128_a_perm_inv :: "16 word \<Rightarrow> 16 word \<Rightarrow> (16 word \<times> 16 word)" where
  "sparx_64_128_a_perm_inv l r = (
    let r1 = xor r l;
        r2 = sparx_64_128_rol r1 14;
        l1 = l - r2;
        l2 = sparx_64_128_rol l1 7
    in (l2, r2))"


definition sparx_64_128_l_w :: "16 word \<Rightarrow> 16 word" where
  "sparx_64_128_l_w x = sparx_64_128_rol x 8"


definition sparx_64_128_linear_layer :: "16 word list \<Rightarrow> 16 word list" where
  "sparx_64_128_linear_layer s = (
    let x0 = s ! 0; x1 = s ! 1; x2 = s ! 2; x3 = s ! 3;
        t = sparx_64_128_l_w (xor x0 x1)
    in [xor x2 (xor x0 t), xor x3 (xor x1 t), x0, x1])"


definition sparx_64_128_linear_layer_inv :: "16 word list \<Rightarrow> 16 word list" where
  "sparx_64_128_linear_layer_inv s = (
    let y0 = s ! 0; y1 = s ! 1; y2 = s ! 2; y3 = s ! 3;
        x0 = y2; x1 = y3;
        t = sparx_64_128_l_w (xor x0 x1)
    in [x0, x1, xor y0 (xor x0 t), xor y1 (xor x1 t)])"


definition sparx_64_128_apply_encrypt_round ::
  "16 word \<Rightarrow> 16 word \<Rightarrow> 16 word \<Rightarrow> 16 word \<Rightarrow> (16 word \<times> 16 word)" where
  "sparx_64_128_apply_encrypt_round x0 x1 key1 key2 = (
    let x0' = xor x0 key1;
        x1' = xor x1 key2
    in sparx_64_128_a_perm x0' x1')"


definition sparx_64_128_apply_decrypt_round ::
  "16 word \<Rightarrow> 16 word \<Rightarrow> 16 word \<Rightarrow> 16 word \<Rightarrow> (16 word \<times> 16 word)" where
  "sparx_64_128_apply_decrypt_round x0 x1 key1 key2 = (
    let (x0', x1') = sparx_64_128_a_perm_inv x0 x1
    in (xor x0' key1, xor x1' key2))"


definition sparx_64_128_extract_key_words :: "128 word \<Rightarrow> 16 word list" where
  "sparx_64_128_extract_key_words master_key =
    [ucast master_key,
     ucast (drop_bit 16 master_key),
     ucast (drop_bit 32 master_key),
     ucast (drop_bit 48 master_key),
     ucast (drop_bit 64 master_key),
     ucast (drop_bit 80 master_key),
     ucast (drop_bit 96 master_key),
     ucast (drop_bit 112 master_key)]"


definition sparx_64_128_k_perm :: "16 word list \<Rightarrow> nat \<Rightarrow> 16 word list" where
  "sparx_64_128_k_perm k c = (
    let (k0, k1) = sparx_64_128_a_perm (k ! 0) (k ! 1);
        k2 = (k ! 2) + k0;
        k3 = (k ! 3) + k1;
        k7 = (k ! 7) + (word_of_nat c)
    in [k ! 6, k7, k0, k1, k2, k3, k ! 4, k ! 5])"


function sparx_64_128_gen_key_schedule_iterate ::
  "16 word list \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> 16 word list list \<Rightarrow> 16 word list list" where
  "sparx_64_128_gen_key_schedule_iterate k c max_c acc = (
    if c \<ge> max_c then acc
    else
      let row = take (2 * sparx_64_128_rounds_per_step) k;
          k' = sparx_64_128_k_perm k (c + 1)
      in sparx_64_128_gen_key_schedule_iterate k' (c + 1) max_c (acc @ [row]))"
  by pat_completeness auto
termination
  by (relation "measure (\<lambda>(k, c, max_c, acc). max_c - c)") auto


definition sparx_64_128_generate_key_schedule :: "128 word \<Rightarrow> 16 word list list" where
  "sparx_64_128_generate_key_schedule master_key = (
    let k = sparx_64_128_extract_key_words master_key;
        max_c = sparx_64_128_n_branches * sparx_64_128_n_steps + 1
    in sparx_64_128_gen_key_schedule_iterate k 0 max_c [])"


definition sparx_64_128_block_to_words :: "64 word \<Rightarrow> 16 word list" where
  "sparx_64_128_block_to_words block =
    [ucast block,
     ucast (drop_bit 16 block),
     ucast (drop_bit 32 block),
     ucast (drop_bit 48 block)]"


definition sparx_64_128_words_to_block :: "16 word list \<Rightarrow> 64 word" where
  "sparx_64_128_words_to_block words =
    or (push_bit 48 (ucast (words ! 3)))
       (or (push_bit 32 (ucast (words ! 2)))
           (or (push_bit 16 (ucast (words ! 1)))
               (ucast (words ! 0))))"


function sparx_64_128_encrypt_round_iterate ::
  "16 word \<Rightarrow> 16 word \<Rightarrow> 16 word list list \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> (16 word \<times> 16 word)" where
  "sparx_64_128_encrypt_round_iterate x0 x1 all_keys row r = (
    if r \<ge> sparx_64_128_rounds_per_step then (x0, x1)
    else
      let key1 = (all_keys ! row) ! (2 * r);
          key2 = (all_keys ! row) ! (2 * r + 1);
          (x0', x1') = sparx_64_128_apply_encrypt_round x0 x1 key1 key2
      in sparx_64_128_encrypt_round_iterate x0' x1' all_keys row (r + 1))"
  by pat_completeness auto
termination
  by (relation "measure (\<lambda>(x0, x1, all_keys, row, r). sparx_64_128_rounds_per_step - r)") auto


function sparx_64_128_decrypt_round_iterate ::
  "16 word \<Rightarrow> 16 word \<Rightarrow> 16 word list list \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> (16 word \<times> 16 word)" where
  "sparx_64_128_decrypt_round_iterate x0 x1 all_keys row r = (
    if r > sparx_64_128_rounds_per_step then (x0, x1)
    else
      let key1 = (all_keys ! row) ! (2 * r);
          key2 = (all_keys ! row) ! (2 * r + 1);
          (x0', x1') = sparx_64_128_apply_decrypt_round x0 x1 key1 key2
      in if r = 0 then (x0', x1')
         else sparx_64_128_decrypt_round_iterate x0' x1' all_keys row (r - 1))"
  by pat_completeness auto
termination
  by (relation "measure (\<lambda>(x0, x1, all_keys, row, r). r)") auto


definition sparx_64_128_encrypt_step_iterate ::
  "16 word list \<Rightarrow> 16 word list list \<Rightarrow> nat \<Rightarrow> 16 word list" where
  "sparx_64_128_encrypt_step_iterate state all_keys step = (
    let row0 = sparx_64_128_n_branches * step;
        (s0, s1) = sparx_64_128_encrypt_round_iterate (state ! 0) (state ! 1) all_keys row0 0;
        (s2, s3) = sparx_64_128_encrypt_round_iterate (state ! 2) (state ! 3) all_keys (row0 + 1) 0
    in [s0, s1, s2, s3])"


definition sparx_64_128_decrypt_step_iterate ::
  "16 word list \<Rightarrow> 16 word list list \<Rightarrow> nat \<Rightarrow> 16 word list" where
  "sparx_64_128_decrypt_step_iterate state all_keys step = (
    let row0 = sparx_64_128_n_branches * step;
        (s0, s1) = sparx_64_128_decrypt_round_iterate (state ! 0) (state ! 1) all_keys row0
                     (sparx_64_128_rounds_per_step - 1);
        (s2, s3) = sparx_64_128_decrypt_round_iterate (state ! 2) (state ! 3) all_keys (row0 + 1)
                     (sparx_64_128_rounds_per_step - 1)
    in [s0, s1, s2, s3])"


function sparx_64_128_encrypt_steps_iterate ::
  "16 word list \<Rightarrow> 16 word list list \<Rightarrow> nat \<Rightarrow> 16 word list" where
  "sparx_64_128_encrypt_steps_iterate state all_keys step = (
    if step \<ge> sparx_64_128_n_steps then state
    else
      let state' = sparx_64_128_encrypt_step_iterate state all_keys step;
          state'' = sparx_64_128_linear_layer state'
      in sparx_64_128_encrypt_steps_iterate state'' all_keys (step + 1))"
  by pat_completeness auto
termination
  by (relation "measure (\<lambda>(state, all_keys, step). sparx_64_128_n_steps - step)") auto


function sparx_64_128_decrypt_steps_iterate ::
  "16 word list \<Rightarrow> 16 word list list \<Rightarrow> nat \<Rightarrow> 16 word list" where
  "sparx_64_128_decrypt_steps_iterate state all_keys step = (
    let state' = sparx_64_128_linear_layer_inv state;
        state'' = sparx_64_128_decrypt_step_iterate state' all_keys step
    in if step = 0 then state''
       else sparx_64_128_decrypt_steps_iterate state'' all_keys (step - 1))"
  by pat_completeness auto
termination
  by (relation "measure (\<lambda>(state, all_keys, step). step)") auto


definition sparx_64_128_encrypt_block ::
  "64 word \<Rightarrow> 16 word list list \<Rightarrow> 64 word" where
  "sparx_64_128_encrypt_block plaintext all_keys = (
    let state = sparx_64_128_block_to_words plaintext;
        state' = sparx_64_128_encrypt_steps_iterate state all_keys 0;
        whitening_row = sparx_64_128_n_branches * sparx_64_128_n_steps;
        wk = all_keys ! whitening_row;
        state_final = [xor (state' ! 0) (wk ! 0), xor (state' ! 1) (wk ! 1),
                        xor (state' ! 2) (wk ! 2), xor (state' ! 3) (wk ! 3)]
    in sparx_64_128_words_to_block state_final)"


definition sparx_64_128_decrypt_block ::
  "64 word \<Rightarrow> 16 word list list \<Rightarrow> 64 word" where
  "sparx_64_128_decrypt_block ciphertext all_keys = (
    let state = sparx_64_128_block_to_words ciphertext;
        whitening_row = sparx_64_128_n_branches * sparx_64_128_n_steps;
        wk = all_keys ! whitening_row;
        state_unwhitened = [xor (state ! 0) (wk ! 0), xor (state ! 1) (wk ! 1),
                             xor (state ! 2) (wk ! 2), xor (state ! 3) (wk ! 3)];
        state' = sparx_64_128_decrypt_steps_iterate state_unwhitened all_keys (sparx_64_128_n_steps - 1)
    in sparx_64_128_words_to_block state')"


definition sparx_64_128_encrypt :: "64 word \<Rightarrow> 128 word \<Rightarrow> 64 word" where
  "sparx_64_128_encrypt plaintext master_key = (
    let all_keys = sparx_64_128_generate_key_schedule master_key
    in sparx_64_128_encrypt_block plaintext all_keys)"


definition sparx_64_128_decrypt :: "64 word \<Rightarrow> 128 word \<Rightarrow> 64 word" where
  "sparx_64_128_decrypt ciphertext master_key = (
    let all_keys = sparx_64_128_generate_key_schedule master_key
    in sparx_64_128_decrypt_block ciphertext all_keys)"


text \<open>Official test vector (CryptoLUX reference implementation,
  https://github.com/cryptolu/SPARX, ref-c/sparx.c).\<close>

definition sparx_64_128_test_key :: "128 word" where
  "sparx_64_128_test_key = 0xeeffccddaabb88996677445522330011"

definition sparx_64_128_test_plaintext :: "64 word" where
  "sparx_64_128_test_plaintext = 0xcdef89ab45670123"

definition sparx_64_128_test_ciphertext :: "64 word" where
  "sparx_64_128_test_ciphertext = 0x5f9801f5f1522bbe"

lemma sparx_64_128_test_vector_encrypt_correct:
  "sparx_64_128_encrypt sparx_64_128_test_plaintext sparx_64_128_test_key
   = sparx_64_128_test_ciphertext"
  by eval

lemma sparx_64_128_test_vector_decrypt_correct:
  "sparx_64_128_decrypt sparx_64_128_test_ciphertext sparx_64_128_test_key
   = sparx_64_128_test_plaintext"
  by eval

end
