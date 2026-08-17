theory Gift_Cofb_128_128
  imports
    "HOL-Library.Word"
    "HOL.Bit_Operations"
begin

section \<open>GIFT-COFB-128/128: Tiered Core Definitions\<close>

subsection \<open>T1: Constants\<close>

definition gift_cofb_128_128_block_size :: nat where
  "gift_cofb_128_128_block_size = 128"

definition gift_cofb_128_128_key_size :: nat where
  "gift_cofb_128_128_key_size = 128"

definition gift_cofb_128_128_nonce_size :: nat where
  "gift_cofb_128_128_nonce_size = 128"

definition gift_cofb_128_128_tag_size :: nat where
  "gift_cofb_128_128_tag_size = 128"

definition gift_cofb_128_128_rounds :: nat where
  "gift_cofb_128_128_rounds = 40"

definition gift_cofb_128_128_rconst :: "32 word list" where
  "gift_cofb_128_128_rconst =
     [0x10000008, 0x80018000, 0x54000002, 0x01010181,
      0x8000001f, 0x10888880, 0x6001e000, 0x51500002,
      0x03030180, 0x8000002f, 0x10088880, 0x60016000,
      0x41500002, 0x03030080, 0x80000027, 0x10008880,
      0x4001e000, 0x11500002, 0x03020180, 0x8000002b,
      0x10080880, 0x60014000, 0x01400002, 0x02020080,
      0x80000021, 0x10000080, 0x0001c000, 0x51000002,
      0x03010180, 0x8000002e, 0x10088800, 0x60012000,
      0x40500002, 0x01030080, 0x80000006, 0x10008808,
      0xc001a000, 0x14500002, 0x01020181, 0x8000001a]"


subsection \<open>Untagged byte/word helpers\<close>

definition bytes_to_word_be :: "8 word list \<Rightarrow> 32 word" where
  "bytes_to_word_be bs = foldl (\<lambda>acc b. or (push_bit 8 acc) (ucast b)) (0 :: 32 word) bs"

definition word_to_bytes_be :: "32 word \<Rightarrow> 8 word list" where
  "word_to_bytes_be w = [ucast (drop_bit 24 w), ucast (drop_bit 16 w), ucast (drop_bit 8 w), ucast w]"

definition bytes_to_word_le :: "8 word list \<Rightarrow> 32 word" where
  "bytes_to_word_le bs =
     or (or (ucast (bs ! 0)) (push_bit 8 (ucast (bs ! 1))))
        (or (push_bit 16 (ucast (bs ! 2))) (push_bit 24 (ucast (bs ! 3))))"

definition word_to_bytes_le :: "32 word \<Rightarrow> 8 word list" where
  "word_to_bytes_le w = [ucast w, ucast (drop_bit 8 w), ucast (drop_bit 16 w), ucast (drop_bit 24 w)]"

definition gift_cofb_128_128_ror32 :: "32 word \<Rightarrow> nat \<Rightarrow> 32 word" where
  "gift_cofb_128_128_ror32 x y = or (drop_bit y x) (push_bit (32 - y) x)"

definition gift_cofb_128_128_swapmove_self :: "32 word \<Rightarrow> 32 word \<Rightarrow> nat \<Rightarrow> 32 word" where
  "gift_cofb_128_128_swapmove_self v msk n =
     (let tmp = and (xor v (drop_bit n v)) msk;
          v1 = xor v tmp
      in xor v1 (push_bit n tmp))"


subsection \<open>T2: Primitives\<close>

definition gift_cofb_128_128_sbox :: "32 word list \<Rightarrow> 32 word list" where
  "gift_cofb_128_128_sbox st =
     (let s0 = st ! 0; s1 = st ! 1; s2 = st ! 2; s3 = st ! 3;
          s1a = xor s1 (and s0 s2);
          s0a = xor s0 (and s1a s3);
          s2a = xor s2 (or s0a s1a);
          s3a = xor s3 s2a;
          s1b = xor s1a s3a;
          s3b = not s3a;
          s2b = xor s2a (and s0a s1b)
      in [s0a, s1b, s2b, s3b])"

definition gift_cofb_128_128_double_half_block :: "8 word list \<Rightarrow> 8 word list" where
  "gift_cofb_128_128_double_half_block offset =
     (let x0 = bytes_to_word_le (take 4 offset);
          x1 = bytes_to_word_le (take 4 (drop 4 offset));
          new_x0 = or (or (push_bit 1 (and x0 0x7f7f7f7f)) (drop_bit 15 (and x0 0x80808080)))
                      (push_bit 17 (and x1 0x80808080));
          new_x1 = xor (or (push_bit 1 (and x1 0x7f7f7f7f)) (drop_bit 15 (and x1 0x80808080)))
                       (push_bit 24 ((and (drop_bit 7 x0) 1) * 27))
      in word_to_bytes_le new_x0 @ word_to_bytes_le new_x1)"

definition gift_cofb_128_128_triple_half_block :: "8 word list \<Rightarrow> 8 word list" where
  "gift_cofb_128_128_triple_half_block offset =
     (let doubled = gift_cofb_128_128_double_half_block offset
      in map (\<lambda>p. xor (fst p) (snd p)) (zip doubled offset))"

definition gift_cofb_128_128_g_function :: "8 word list \<Rightarrow> 8 word list" where
  "gift_cofb_128_128_g_function y =
     (let tmp0 = bytes_to_word_le (take 4 y);
          tmp1 = bytes_to_word_le (take 4 (drop 4 y));
          new_y2 = or (or (push_bit 1 (and tmp0 0x7f7f7f7f)) (drop_bit 15 (and tmp0 0x80808080)))
                      (push_bit 17 (and tmp1 0x80808080));
          new_y3 = or (or (push_bit 1 (and tmp1 0x7f7f7f7f)) (drop_bit 15 (and tmp1 0x80808080)))
                      (push_bit 17 (and tmp0 0x80808080))
      in take 4 (drop 8 y) @ take 4 (drop 12 y) @ word_to_bytes_le new_y2 @ word_to_bytes_le new_y3)"


subsection \<open>T3: Structural Components\<close>

definition gift_cofb_128_128_key_update :: "32 word \<Rightarrow> 32 word" where
  "gift_cofb_128_128_key_update x =
     or (or (and (drop_bit 12 x) 0x0000000f) (push_bit 4 (and x 0x00000fff)))
        (or (and (drop_bit 2 x) 0x3fff0000) (push_bit 14 (and x 0x00030000)))"

definition gift_cofb_128_128_rearrange_rkey_0 :: "32 word \<Rightarrow> 32 word" where
  "gift_cofb_128_128_rearrange_rkey_0 x =
     (let x = gift_cofb_128_128_swapmove_self x 0x00550055 9;
          x = gift_cofb_128_128_swapmove_self x 0x000f000f 12;
          x = gift_cofb_128_128_swapmove_self x 0x00003333 18;
          x = gift_cofb_128_128_swapmove_self x 0x000000ff 24
      in x)"

definition gift_cofb_128_128_rearrange_rkey_1 :: "32 word \<Rightarrow> 32 word" where
  "gift_cofb_128_128_rearrange_rkey_1 x =
     (let x = gift_cofb_128_128_swapmove_self x 0x11111111 3;
          x = gift_cofb_128_128_swapmove_self x 0x03030303 6;
          x = gift_cofb_128_128_swapmove_self x 0x000f000f 12;
          x = gift_cofb_128_128_swapmove_self x 0x000000ff 24
      in x)"

definition gift_cofb_128_128_rearrange_rkey_2 :: "32 word \<Rightarrow> 32 word" where
  "gift_cofb_128_128_rearrange_rkey_2 x =
     (let x = gift_cofb_128_128_swapmove_self x 0x0000aaaa 15;
          x = gift_cofb_128_128_swapmove_self x 0x00003333 18;
          x = gift_cofb_128_128_swapmove_self x 0x0000f0f0 12;
          x = gift_cofb_128_128_swapmove_self x 0x000000ff 24
      in x)"

definition gift_cofb_128_128_rearrange_rkey_3 :: "32 word \<Rightarrow> 32 word" where
  "gift_cofb_128_128_rearrange_rkey_3 x =
     (let x = gift_cofb_128_128_swapmove_self x 0x0a0a0a0a 3;
          x = gift_cofb_128_128_swapmove_self x 0x00cc00cc 6;
          x = gift_cofb_128_128_swapmove_self x 0x0000f0f0 12;
          x = gift_cofb_128_128_swapmove_self x 0x000000ff 24
      in x)"

definition gift_cofb_128_128_key_triple_update_0 :: "32 word \<Rightarrow> 32 word" where
  "gift_cofb_128_128_key_triple_update_0 x =
     or (gift_cofb_128_128_ror32 (and x 0x33333333) 24) (gift_cofb_128_128_ror32 (and x 0xcccccccc) 16)"

definition gift_cofb_128_128_key_double_update_1 :: "32 word \<Rightarrow> 32 word" where
  "gift_cofb_128_128_key_double_update_1 x =
     or (or (and (drop_bit 4 x) 0x0f000f00) (push_bit 4 (and x 0x0f000f00)))
        (or (and (drop_bit 6 x) 0x00030003) (push_bit 2 (and x 0x003f003f)))"

definition gift_cofb_128_128_key_triple_update_1 :: "32 word \<Rightarrow> 32 word" where
  "gift_cofb_128_128_key_triple_update_1 x =
     or (or (and (drop_bit 6 x) 0x03000300) (push_bit 2 (and x 0x3f003f00)))
        (or (and (drop_bit 5 x) 0x00070007) (push_bit 3 (and x 0x001f001f)))"

definition gift_cofb_128_128_key_double_update_2 :: "32 word \<Rightarrow> 32 word" where
  "gift_cofb_128_128_key_double_update_2 x =
     or (gift_cofb_128_128_ror32 (and x 0xaaaaaaaa) 24) (gift_cofb_128_128_ror32 (and x 0x55555555) 16)"

definition gift_cofb_128_128_key_triple_update_2 :: "32 word \<Rightarrow> 32 word" where
  "gift_cofb_128_128_key_triple_update_2 x =
     or (gift_cofb_128_128_ror32 (and x 0x55555555) 24) (gift_cofb_128_128_ror32 (and x 0xaaaaaaaa) 20)"

definition gift_cofb_128_128_key_double_update_3 :: "32 word \<Rightarrow> 32 word" where
  "gift_cofb_128_128_key_double_update_3 x =
     or (or (and (drop_bit 2 x) 0x03030303) (push_bit 2 (and x 0x03030303)))
        (or (and (drop_bit 1 x) 0x70707070) (push_bit 3 (and x 0x10101010)))"

definition gift_cofb_128_128_key_triple_update_3 :: "32 word \<Rightarrow> 32 word" where
  "gift_cofb_128_128_key_triple_update_3 x =
     or (or (or (and (drop_bit 18 x) 0x00003030) (push_bit 3 (and x 0x01010101)))
            (or (and (drop_bit 14 x) 0x0000c0c0) (push_bit 15 (and x 0x0000e0e0))))
        (or (and (drop_bit 1 x) 0x07070707) (push_bit 19 (and x 0x00001010)))"

definition gift_cofb_128_128_key_double_update_4 :: "32 word \<Rightarrow> 32 word" where
  "gift_cofb_128_128_key_double_update_4 x =
     or (or (and (drop_bit 4 x) 0x0fff0000) (push_bit 12 (and x 0x000f0000)))
        (or (and (drop_bit 8 x) 0x000000ff) (push_bit 8 (and x 0x000000ff)))"

definition gift_cofb_128_128_key_triple_update_4 :: "32 word \<Rightarrow> 32 word" where
  "gift_cofb_128_128_key_triple_update_4 x =
     or (or (and (drop_bit 6 x) 0x03ff0000) (push_bit 10 (and x 0x003f0000)))
        (or (and (drop_bit 4 x) 0x00000fff) (push_bit 12 (and x 0x0000000f)))"

definition gift_cofb_128_128_phase4_step :: "32 word list \<Rightarrow> nat \<Rightarrow> 32 word list" where
  "gift_cofb_128_128_phase4_step rkey i =
     (let v0 = gift_cofb_128_128_key_triple_update_0 (rkey ! (i - 20));
          v1 = gift_cofb_128_128_key_double_update_1 (rkey ! (i - 17));
          v2 = gift_cofb_128_128_key_triple_update_1 (rkey ! (i - 18));
          v3 = gift_cofb_128_128_key_double_update_2 (rkey ! (i - 15));
          v4 = gift_cofb_128_128_key_triple_update_2 (rkey ! (i - 16));
          v5 = gift_cofb_128_128_key_double_update_3 (rkey ! (i - 13));
          v6 = gift_cofb_128_128_key_triple_update_3 (rkey ! (i - 14));
          v7 = gift_cofb_128_128_key_double_update_4 (rkey ! (i - 11));
          v8 = gift_cofb_128_128_key_triple_update_4 (rkey ! (i - 12));
          base = rkey ! (i - 19);
          rkey_a = rkey[i := base, i + 1 := v0, i + 2 := v1, i + 3 := v2, i + 4 := v3,
                        i + 5 := v4, i + 6 := v5, i + 7 := v6, i + 8 := v7, i + 9 := v8];
          rkey_b = rkey_a[i := gift_cofb_128_128_swapmove_self (rkey_a ! i) 0x00003333 16];
          rkey_c = rkey_b[i := gift_cofb_128_128_swapmove_self (rkey_b ! i) 0x55554444 1];
          rkey_d = rkey_c[i + 1 := gift_cofb_128_128_swapmove_self (rkey_c ! (i + 1)) 0x55551100 1]
      in rkey_d)"

definition gift_cofb_128_128_precompute_round_keys :: "8 word list \<Rightarrow> 32 word list" where
  "gift_cofb_128_128_precompute_round_keys key =
     (let w0 = bytes_to_word_be (take 4 key);
          w1 = bytes_to_word_be (take 4 (drop 4 key));
          w2 = bytes_to_word_be (take 4 (drop 8 key));
          w3 = bytes_to_word_be (take 4 (drop 12 key));
          rk = replicate 80 (0 :: 32 word);
          rk = rk[0 := w3, 1 := w1, 2 := w2, 3 := w0];
          rk = rk[4 := rk ! 1, 5 := gift_cofb_128_128_key_update (rk ! 0)];
          rk = rk[6 := rk ! 3, 7 := gift_cofb_128_128_key_update (rk ! 2)];
          rk = rk[8 := rk ! 5, 9 := gift_cofb_128_128_key_update (rk ! 4)];
          rk = rk[10 := rk ! 7, 11 := gift_cofb_128_128_key_update (rk ! 6)];
          rk = rk[12 := rk ! 9, 13 := gift_cofb_128_128_key_update (rk ! 8)];
          rk = rk[14 := rk ! 11, 15 := gift_cofb_128_128_key_update (rk ! 10)];
          rk = rk[16 := rk ! 13, 17 := gift_cofb_128_128_key_update (rk ! 12)];
          rk = rk[18 := rk ! 15, 19 := gift_cofb_128_128_key_update (rk ! 14)];
          rk = rk[0 := gift_cofb_128_128_rearrange_rkey_0 (rk ! 0),
                  1 := gift_cofb_128_128_rearrange_rkey_0 (rk ! 1),
                  2 := gift_cofb_128_128_rearrange_rkey_1 (rk ! 2),
                  3 := gift_cofb_128_128_rearrange_rkey_1 (rk ! 3),
                  4 := gift_cofb_128_128_rearrange_rkey_2 (rk ! 4),
                  5 := gift_cofb_128_128_rearrange_rkey_2 (rk ! 5),
                  6 := gift_cofb_128_128_rearrange_rkey_3 (rk ! 6),
                  7 := gift_cofb_128_128_rearrange_rkey_3 (rk ! 7)];
          rk = rk[10 := gift_cofb_128_128_rearrange_rkey_0 (rk ! 10),
                  11 := gift_cofb_128_128_rearrange_rkey_0 (rk ! 11),
                  12 := gift_cofb_128_128_rearrange_rkey_1 (rk ! 12),
                  13 := gift_cofb_128_128_rearrange_rkey_1 (rk ! 13),
                  14 := gift_cofb_128_128_rearrange_rkey_2 (rk ! 14),
                  15 := gift_cofb_128_128_rearrange_rkey_2 (rk ! 15),
                  16 := gift_cofb_128_128_rearrange_rkey_3 (rk ! 16),
                  17 := gift_cofb_128_128_rearrange_rkey_3 (rk ! 17)];
          rk = gift_cofb_128_128_phase4_step rk 20;
          rk = gift_cofb_128_128_phase4_step rk 30;
          rk = gift_cofb_128_128_phase4_step rk 40;
          rk = gift_cofb_128_128_phase4_step rk 50;
          rk = gift_cofb_128_128_phase4_step rk 60;
          rk = gift_cofb_128_128_phase4_step rk 70
      in rk)"

definition gift_cofb_128_128_quintuple_round ::
  "32 word list \<Rightarrow> 32 word list \<Rightarrow> 32 word list \<Rightarrow> 32 word list" where
  "gift_cofb_128_128_quintuple_round state rkey rconst =
     (let s = gift_cofb_128_128_sbox state;
          s3 = or (and (drop_bit 1 (s!3)) 0x77777777) (push_bit 3 (and (s!3) 0x11111111));
          s1 = or (and (drop_bit 2 (s!1)) 0x33333333) (push_bit 2 (and (s!1) 0x33333333));
          s2 = or (and (drop_bit 3 (s!2)) 0x11111111) (push_bit 1 (and (s!2) 0x77777777));
          s1 = xor s1 (rkey ! 0); s2 = xor s2 (rkey ! 1); s0 = xor (s!0) (rconst ! 0);
          s = gift_cofb_128_128_sbox [s3, s1, s2, s0];
          s0 = or (and (drop_bit 4 (s!3)) 0x0fff0fff) (push_bit 12 (and (s!3) 0x000f000f));
          s1 = or (and (drop_bit 8 (s!1)) 0x00ff00ff) (push_bit 8 (and (s!1) 0x00ff00ff));
          s2 = or (and (drop_bit 12 (s!2)) 0x000f000f) (push_bit 4 (and (s!2) 0x0fff0fff));
          s1 = xor s1 (rkey ! 2); s2 = xor s2 (rkey ! 3); s3 = xor (s!0) (rconst ! 1);
          s = gift_cofb_128_128_sbox [s0, s1, s2, s3];
          s3 = gift_cofb_128_128_ror32 (s!3) 16;
          s2 = gift_cofb_128_128_ror32 (s!2) 16;
          s1 = gift_cofb_128_128_swapmove_self (s!1) 0x55555555 1;
          s2 = gift_cofb_128_128_swapmove_self s2 0x00005555 1;
          s3 = gift_cofb_128_128_swapmove_self s3 0x55550000 1;
          s1 = xor s1 (rkey ! 4); s2 = xor s2 (rkey ! 5); s0 = xor (s!0) (rconst ! 2);
          s = gift_cofb_128_128_sbox [s3, s1, s2, s0];
          s0 = or (and (drop_bit 6 (s!3)) 0x03030303) (push_bit 2 (and (s!3) 0x3f3f3f3f));
          s1 = or (and (drop_bit 4 (s!1)) 0x0f0f0f0f) (push_bit 4 (and (s!1) 0x0f0f0f0f));
          s2 = or (and (drop_bit 2 (s!2)) 0x3f3f3f3f) (push_bit 6 (and (s!2) 0x03030303));
          s1 = xor s1 (rkey ! 6); s2 = xor s2 (rkey ! 7); s3 = xor (s!0) (rconst ! 3);
          s = gift_cofb_128_128_sbox [s0, s1, s2, s3];
          s3 = gift_cofb_128_128_ror32 (s!3) 24;
          s1 = gift_cofb_128_128_ror32 (s!1) 16;
          s2 = gift_cofb_128_128_ror32 (s!2) 8;
          s1 = xor s1 (rkey ! 8); s2 = xor s2 (rkey ! 9); s0 = xor (s!0) (rconst ! 4);
          s0 = xor s0 s3; s3 = xor s3 s0; s0 = xor s0 s3
      in [s0, s1, s2, s3])"

definition gift_cofb_128_128_permutation :: "8 word list \<Rightarrow> 32 word list \<Rightarrow> 8 word list" where
  "gift_cofb_128_128_permutation block rkey =
     (let state = [bytes_to_word_be (take 4 block), bytes_to_word_be (take 4 (drop 4 block)),
                   bytes_to_word_be (take 4 (drop 8 block)), bytes_to_word_be (take 4 (drop 12 block))];
          state = gift_cofb_128_128_quintuple_round state (take 10 rkey) (take 5 gift_cofb_128_128_rconst);
          state = gift_cofb_128_128_quintuple_round state (take 10 (drop 10 rkey)) (take 5 (drop 5 gift_cofb_128_128_rconst));
          state = gift_cofb_128_128_quintuple_round state (take 10 (drop 20 rkey)) (take 5 (drop 10 gift_cofb_128_128_rconst));
          state = gift_cofb_128_128_quintuple_round state (take 10 (drop 30 rkey)) (take 5 (drop 15 gift_cofb_128_128_rconst));
          state = gift_cofb_128_128_quintuple_round state (take 10 (drop 40 rkey)) (take 5 (drop 20 gift_cofb_128_128_rconst));
          state = gift_cofb_128_128_quintuple_round state (take 10 (drop 50 rkey)) (take 5 (drop 25 gift_cofb_128_128_rconst));
          state = gift_cofb_128_128_quintuple_round state (take 10 (drop 60 rkey)) (take 5 (drop 30 gift_cofb_128_128_rconst));
          state = gift_cofb_128_128_quintuple_round state (take 10 (drop 70 rkey)) (take 5 (drop 35 gift_cofb_128_128_rconst))
      in word_to_bytes_be (state ! 0) @ word_to_bytes_be (state ! 1) @ word_to_bytes_be (state ! 2) @ word_to_bytes_be (state ! 3))"


subsection \<open>T4: Orchestration (COFB mode)\<close>

definition gift_cofb_128_128_padding :: "8 word list \<Rightarrow> nat \<Rightarrow> 8 word list" where
  "gift_cofb_128_128_padding data n =
     (if n \<ge> 16 then take 16 data
      else take n data @ [0x80] @ replicate (15 - n) (0 :: 8 word))"

definition gift_cofb_128_128_initialize ::
  "8 word list \<Rightarrow> 8 word list \<Rightarrow> (8 word list \<times> 8 word list \<times> 32 word list)" where
  "gift_cofb_128_128_initialize key nonce =
     (let rkey = gift_cofb_128_128_precompute_round_keys key;
          y = gift_cofb_128_128_permutation nonce rkey;
          offset = take 8 y
      in (y, offset, rkey))"

function gift_cofb_128_128_process_ad_blocks_loop ::
  "8 word list \<Rightarrow> 8 word list \<Rightarrow> 8 word list \<Rightarrow> 32 word list \<Rightarrow> (8 word list \<times> 8 word list \<times> 8 word list)" where
  "gift_cofb_128_128_process_ad_blocks_loop ad y offset rkey =
     (if length ad \<le> 16 then (ad, y, offset)
      else
        let block = take 16 ad;
            g_y = gift_cofb_128_128_g_function y;
            input0 = map (\<lambda>p. xor (fst p) (snd p)) (zip (gift_cofb_128_128_padding block 16) g_y);
            offset2 = gift_cofb_128_128_double_half_block offset;
            input1 = map (\<lambda>p. xor (fst p) (snd p)) (zip (take 8 input0) offset2) @ drop 8 input0;
            y2 = gift_cofb_128_128_permutation input1 rkey
        in gift_cofb_128_128_process_ad_blocks_loop (drop 16 ad) y2 offset2 rkey)"
  by pat_completeness auto

termination gift_cofb_128_128_process_ad_blocks_loop
  by (relation "measure (\<lambda>(ad, y, offset, rkey). length ad)") auto

definition gift_cofb_128_128_process_associated_data ::
  "8 word list \<Rightarrow> 8 word list \<Rightarrow> 8 word list \<Rightarrow> 32 word list \<Rightarrow> bool \<Rightarrow> (8 word list \<times> 8 word list \<times> 8 word list)" where
  "gift_cofb_128_128_process_associated_data ad y offset rkey empty_m =
     (let (ad_rem, y2, offset2) = gift_cofb_128_128_process_ad_blocks_loop ad y offset rkey;
          empty_a = (length ad = 0);
          offset3 = gift_cofb_128_128_triple_half_block offset2;
          offset4 = if (length ad_rem mod 16 \<noteq> 0) \<or> empty_a
                    then gift_cofb_128_128_triple_half_block offset3 else offset3;
          offset5 = if empty_m
                    then gift_cofb_128_128_triple_half_block (gift_cofb_128_128_triple_half_block offset4)
                    else offset4
      in (y2, offset5, ad_rem))"

function gift_cofb_128_128_encrypt_blocks_loop ::
  "8 word list \<Rightarrow> 8 word list \<Rightarrow> 8 word list \<Rightarrow> 32 word list \<Rightarrow> (8 word list \<times> 8 word list \<times> 8 word list)" where
  "gift_cofb_128_128_encrypt_blocks_loop msg y offset rkey =
     (if length msg \<le> 16 then ([], y, offset)
      else
        let block = take 16 msg;
            c_block = map (\<lambda>p. xor (fst p) (snd p)) (zip y block);
            offset2 = gift_cofb_128_128_double_half_block offset;
            g_y = gift_cofb_128_128_g_function y;
            input0 = map (\<lambda>p. xor (fst p) (snd p)) (zip (gift_cofb_128_128_padding block 16) g_y);
            input1 = map (\<lambda>p. xor (fst p) (snd p)) (zip (take 8 input0) offset2) @ drop 8 input0;
            y2 = gift_cofb_128_128_permutation input1 rkey;
            (rest_ct, y3, offset3) = gift_cofb_128_128_encrypt_blocks_loop (drop 16 msg) y2 offset2 rkey
        in (c_block @ rest_ct, y3, offset3))"
  by pat_completeness auto

termination gift_cofb_128_128_encrypt_blocks_loop
  by (relation "measure (\<lambda>(msg, y, offset, rkey). length msg)") auto

function gift_cofb_128_128_decrypt_blocks_loop ::
  "8 word list \<Rightarrow> 8 word list \<Rightarrow> 8 word list \<Rightarrow> 32 word list \<Rightarrow> (8 word list \<times> 8 word list \<times> 8 word list)" where
  "gift_cofb_128_128_decrypt_blocks_loop ct y offset rkey =
     (if length ct \<le> 16 then ([], y, offset)
      else
        let block = take 16 ct;
            m_block = map (\<lambda>p. xor (fst p) (snd p)) (zip y block);
            offset2 = gift_cofb_128_128_double_half_block offset;
            g_y = gift_cofb_128_128_g_function y;
            input0 = map (\<lambda>p. xor (fst p) (snd p)) (zip (gift_cofb_128_128_padding m_block 16) g_y);
            input1 = map (\<lambda>p. xor (fst p) (snd p)) (zip (take 8 input0) offset2) @ drop 8 input0;
            y2 = gift_cofb_128_128_permutation input1 rkey;
            (rest_pt, y3, offset3) = gift_cofb_128_128_decrypt_blocks_loop (drop 16 ct) y2 offset2 rkey
        in (m_block @ rest_pt, y3, offset3))"
  by pat_completeness auto

termination gift_cofb_128_128_decrypt_blocks_loop
  by (relation "measure (\<lambda>(ct, y, offset, rkey). length ct)") auto

definition gift_cofb_128_128_encrypt_message_blocks ::
  "8 word list \<Rightarrow> 8 word list \<Rightarrow> 8 word list \<Rightarrow> 32 word list \<Rightarrow> (8 word list \<times> 8 word list)" where
  "gift_cofb_128_128_encrypt_message_blocks msg y offset rkey =
     (let (ct_full, y2, offset2) = gift_cofb_128_128_encrypt_blocks_loop msg y offset rkey
      in if msg = [] then (ct_full, y2)
         else
           let in_len = length msg - ((length msg - 1) div 16) * 16;
               last_block = drop (length msg - in_len) msg;
               offset3 = gift_cofb_128_128_triple_half_block offset2;
               offset4 = if in_len mod 16 \<noteq> 0 then gift_cofb_128_128_triple_half_block offset3 else offset3;
               c_last = map (\<lambda>p. xor (fst p) (snd p)) (zip (take in_len y2) last_block);
               g_y = gift_cofb_128_128_g_function y2;
               input0 = map (\<lambda>p. xor (fst p) (snd p)) (zip (gift_cofb_128_128_padding last_block in_len) g_y);
               input1 = map (\<lambda>p. xor (fst p) (snd p)) (zip (take 8 input0) offset4) @ drop 8 input0;
               y3 = gift_cofb_128_128_permutation input1 rkey
           in (ct_full @ c_last, take 16 y3))"

definition gift_cofb_128_128_decrypt_message_blocks ::
  "8 word list \<Rightarrow> 8 word list \<Rightarrow> 8 word list \<Rightarrow> 32 word list \<Rightarrow> (8 word list \<times> 8 word list)" where
  "gift_cofb_128_128_decrypt_message_blocks ct y offset rkey =
     (let (pt_full, y2, offset2) = gift_cofb_128_128_decrypt_blocks_loop ct y offset rkey
      in if ct = [] then (pt_full, y2)
         else
           let in_len = length ct - ((length ct - 1) div 16) * 16;
               last_block = drop (length ct - in_len) ct;
               offset3 = gift_cofb_128_128_triple_half_block offset2;
               offset4 = if in_len mod 16 \<noteq> 0 then gift_cofb_128_128_triple_half_block offset3 else offset3;
               m_last = map (\<lambda>p. xor (fst p) (snd p)) (zip (take in_len y2) last_block);
               g_y = gift_cofb_128_128_g_function y2;
               input0 = map (\<lambda>p. xor (fst p) (snd p)) (zip (gift_cofb_128_128_padding m_last in_len) g_y);
               input1 = map (\<lambda>p. xor (fst p) (snd p)) (zip (take 8 input0) offset4) @ drop 8 input0;
               y3 = gift_cofb_128_128_permutation input1 rkey
           in (pt_full @ m_last, take 16 y3))"

definition gift_cofb_128_128_encrypt ::
  "8 word list \<Rightarrow> 8 word list \<Rightarrow> 8 word list \<Rightarrow> 8 word list \<Rightarrow> 8 word list" where
  "gift_cofb_128_128_encrypt key nonce ad plaintext =
     (let (y0, offset0, rkey) = gift_cofb_128_128_initialize key nonce;
          (y1, offset1, ad_rem) = gift_cofb_128_128_process_associated_data ad y0 offset0 rkey (plaintext = []);
          g_y = gift_cofb_128_128_g_function y1;
          input0 = map (\<lambda>p. xor (fst p) (snd p)) (zip (gift_cofb_128_128_padding ad_rem (length ad_rem)) g_y);
          input1 = map (\<lambda>p. xor (fst p) (snd p)) (zip (take 8 input0) offset1) @ drop 8 input0;
          y2 = gift_cofb_128_128_permutation input1 rkey
      in if plaintext = [] then take 16 y2
         else let (ct, tag) = gift_cofb_128_128_encrypt_message_blocks plaintext y2 offset1 rkey in ct @ tag)"

definition gift_cofb_128_128_decrypt ::
  "8 word list \<Rightarrow> 8 word list \<Rightarrow> 8 word list \<Rightarrow> 8 word list \<Rightarrow> 8 word list option" where
  "gift_cofb_128_128_decrypt key nonce ad ciphertext =
     (let tag = drop (length ciphertext - 16) ciphertext;
          body = take (length ciphertext - 16) ciphertext;
          (y0, offset0, rkey) = gift_cofb_128_128_initialize key nonce;
          (y1, offset1, ad_rem) = gift_cofb_128_128_process_associated_data ad y0 offset0 rkey (body = []);
          g_y = gift_cofb_128_128_g_function y1;
          input0 = map (\<lambda>p. xor (fst p) (snd p)) (zip (gift_cofb_128_128_padding ad_rem (length ad_rem)) g_y);
          input1 = map (\<lambda>p. xor (fst p) (snd p)) (zip (take 8 input0) offset1) @ drop 8 input0;
          y2 = gift_cofb_128_128_permutation input1 rkey
      in if body = [] then (if take 16 y2 = tag then Some [] else None)
         else
           let (pt, expected_tag) = gift_cofb_128_128_decrypt_message_blocks body y2 offset1 rkey
           in if expected_tag = tag then Some pt else None)"

end
