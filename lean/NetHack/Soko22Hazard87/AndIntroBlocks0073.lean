import NetHack.Soko22Hazard87.AndIntroBlocks0072
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Soko22Hazard87
open NetHack.Sokoban NetHack.Sokoban.PatternCorrection
theorem andIntro18250 (p : Pattern) (ha : d82099 p = 1) (hb : d99241 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d510 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d7449 q = 1) (hb : d82077 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d7449, d82077, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18246 q ha hb
    | true =>
      simp only [d7449, d82077, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18247 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d6831 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d7450 q = 1) (hb : d82078 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d7450, d82078, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d7450, d82078, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d82079 q = 1) (hb : d99222 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d82079, d99222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d82079, d99222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d82080 q = 1) (hb : d99223 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d82080, d99223, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d82080, d99223, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d82084 q = 1) (hb : d99225 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d82084, d99225, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d82084, d99225, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18248 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d654 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d82085 q = 1) (hb : d99226 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d82085, d99226, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d82085, d99226, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d82086 q = 1) (hb : d99227 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d82086, d99227, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d82086, d99227, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h11 (q : Pattern) (ha : d82087 q = 1) (hb : d99228 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d82087, d99228, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d82087, d99228, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h12 (q : Pattern) (ha : d82088 q = 1) (hb : d99229 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d82088, d99229, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d82088, d99229, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d82094 q = 1) (hb : d99236 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d82094, d99236, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d82094, d99236, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18249 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d737 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d82095 q = 1) (hb : d99237 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d82095, d99237, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d82095, d99237, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d82096 q = 1) (hb : d99238 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d82096, d99238, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d82096, d99238, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h17 (q : Pattern) (ha : d82097 q = 1) (hb : d99239 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d82097, d99239, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d82097, d99239, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h18 (q : Pattern) (ha : d82098 q = 1) (hb : d99240 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d82098, d99240, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d82098, d99240, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h19 (q : Pattern) (ha : d82099 q = 1) (hb : d99241 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d82099, d99241, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d82099, d99241, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro18251 (p : Pattern) (ha : d82105 p = 1) (hb : d99247 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d82100 q = 1) (hb : d99242 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d82100, d99242, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d82100, d99242, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18250 q ha hb
  have h2 (q : Pattern) (ha : d82101 q = 1) (hb : d99243 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d82101, d99243, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d82101, d99243, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d82102 q = 1) (hb : d99244 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d82102, d99244, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d82102, d99244, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d82103 q = 1) (hb : d99245 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d82103, d99245, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d82103, d99245, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d82104 q = 1) (hb : d99246 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d82104, d99246, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d82104, d99246, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d82105 q = 1) (hb : d99247 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d82105, d99247, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d82105, d99247, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro18252 (p : Pattern) (ha : d7587 p = 1) (hb : d82111 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d810 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d819 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d6888 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d7582 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d7583 q = 1) (hb : d82107 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d7583, d82107, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d7583, d82107, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d6161 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d7584 q = 1) (hb : d82108 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d7584, d82108, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d7584, d82108, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d7585 q = 1) (hb : d82109 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d7585, d82109, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d7585, d82109, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d7586 q = 1) (hb : d82110 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d7586, d82110, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d7586, d82110, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d7587 q = 1) (hb : d82111 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d7587, d82111, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7587, d82111, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro18253 (p : Pattern) (ha : d7596 p = 1) (hb : d82116 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d810 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d819 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d6888 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d7582 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d7583 q = 1) (hb : d82107 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d7583, d82107, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d7583, d82107, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d6161 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d7584 q = 1) (hb : d82108 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d7584, d82108, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d7584, d82108, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d7585 q = 1) (hb : d82109 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d7585, d82109, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d7585, d82109, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d7586 q = 1) (hb : d82110 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d7586, d82110, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7586, d82110, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d920 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d925 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d6896 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d7591 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d7592 q = 1) (hb : d82112 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d7592, d82112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d7592, d82112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d6182 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d7593 q = 1) (hb : d82113 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d7593, d82113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d7593, d82113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d7594 q = 1) (hb : d82114 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d7594, d82114, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d7594, d82114, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d7595 q = 1) (hb : d82115 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d7595, d82115, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d7595, d82115, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d7596 q = 1) (hb : d82116 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d7596, d82116, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d7596, d82116, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro18254 (p : Pattern) (ha : d82123 p = 1) (hb : d99251 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d6896 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d7591 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d7592 q = 1) (hb : d82112 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d7592, d82112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d7592, d82112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d6182 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d7593 q = 1) (hb : d82113 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d7593, d82113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d7593, d82113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d7594 q = 1) (hb : d82121 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d7594, d82121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7594, d82121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d7595 q = 1) (hb : d82122 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d7595, d82122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7595, d82122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d82123 q = 1) (hb : d99251 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d82123, d99251, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d82123, d99251, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
  exact h8 p ha hb
theorem andIntro18255 (p : Pattern) (ha : d82133 p = 1) (hb : d99262 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d6934 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d99257 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d82129 q = 1) (hb : d99258 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d82129, d99258, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d82129, d99258, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d6235 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d82130 q = 1) (hb : d99259 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d82130, d99259, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d82130, d99259, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d82131 q = 1) (hb : d99260 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d82131, d99260, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d82131, d99260, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d82132 q = 1) (hb : d99261 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d82132, d99261, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d82132, d99261, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d82133 q = 1) (hb : d99262 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d82133, d99262, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d82133, d99262, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro18256 (p : Pattern) (ha : d82139 p = 1) (hb : d99268 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d802 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d7597 q = 1) (hb : d82117 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d7597, d82117, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18252 q ha hb
    | true =>
      simp only [d7597, d82117, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18253 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d6909 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d7598 q = 1) (hb : d82118 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d7598, d82118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d7598, d82118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d82119 q = 1) (hb : d99249 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d82119, d99249, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d82119, d99249, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d82120 q = 1) (hb : d99250 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d82120, d99250, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d82120, d99250, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d82124 q = 1) (hb : d99252 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d82124, d99252, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d82124, d99252, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18254 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d960 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d82125 q = 1) (hb : d99253 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d82125, d99253, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d82125, d99253, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d82126 q = 1) (hb : d99254 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d82126, d99254, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d82126, d99254, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h11 (q : Pattern) (ha : d82127 q = 1) (hb : d99255 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d82127, d99255, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d82127, d99255, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h12 (q : Pattern) (ha : d82128 q = 1) (hb : d99256 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d82128, d99256, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d82128, d99256, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d82134 q = 1) (hb : d99263 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d82134, d99263, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d82134, d99263, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18255 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d1070 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d82135 q = 1) (hb : d99264 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d82135, d99264, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d82135, d99264, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d82136 q = 1) (hb : d99265 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d82136, d99265, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d82136, d99265, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h17 (q : Pattern) (ha : d82137 q = 1) (hb : d99266 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d82137, d99266, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d82137, d99266, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h18 (q : Pattern) (ha : d82138 q = 1) (hb : d99267 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d82138, d99267, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d82138, d99267, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h19 (q : Pattern) (ha : d82139 q = 1) (hb : d99268 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d82139, d99268, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d82139, d99268, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro18257 (p : Pattern) (ha : d82145 p = 1) (hb : d99274 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d82140 q = 1) (hb : d99269 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d82140, d99269, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d82140, d99269, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18256 q ha hb
  have h2 (q : Pattern) (ha : d82141 q = 1) (hb : d99270 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d82141, d99270, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d82141, d99270, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d82142 q = 1) (hb : d99271 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d82142, d99271, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d82142, d99271, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d82143 q = 1) (hb : d99272 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d82143, d99272, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d82143, d99272, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d82144 q = 1) (hb : d99273 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d82144, d99273, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d82144, d99273, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d82145 q = 1) (hb : d99274 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d82145, d99274, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d82145, d99274, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro18258 (p : Pattern) (ha : d7740 p = 1) (hb : d82152 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1189 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d1198 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d6967 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d7735 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d7736 q = 1) (hb : d82148 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d7736, d82148, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d7736, d82148, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d6300 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d7737 q = 1) (hb : d82149 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d7737, d82149, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d7737, d82149, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d7738 q = 1) (hb : d82150 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d7738, d82150, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d7738, d82150, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d7739 q = 1) (hb : d82151 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d7739, d82151, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d7739, d82151, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d7740 q = 1) (hb : d82152 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d7740, d82152, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7740, d82152, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro18259 (p : Pattern) (ha : d7749 p = 1) (hb : d82157 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1189 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1198 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d6967 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d7735 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d7736 q = 1) (hb : d82148 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d7736, d82148, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d7736, d82148, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d6300 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d7737 q = 1) (hb : d82149 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d7737, d82149, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d7737, d82149, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d7738 q = 1) (hb : d82150 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d7738, d82150, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d7738, d82150, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d7739 q = 1) (hb : d82151 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d7739, d82151, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7739, d82151, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d1331 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d1336 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d6975 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d7744 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d7745 q = 1) (hb : d82153 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d7745, d82153, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d7745, d82153, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d6321 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d7746 q = 1) (hb : d82154 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d7746, d82154, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d7746, d82154, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d7747 q = 1) (hb : d82155 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d7747, d82155, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d7747, d82155, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d7748 q = 1) (hb : d82156 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d7748, d82156, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d7748, d82156, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d7749 q = 1) (hb : d82157 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d7749, d82157, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d7749, d82157, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro18260 (p : Pattern) (ha : d82164 p = 1) (hb : d99279 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d6975 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d7744 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d7745 q = 1) (hb : d82153 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d7745, d82153, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d7745, d82153, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d6321 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d7746 q = 1) (hb : d82154 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d7746, d82154, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d7746, d82154, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d7747 q = 1) (hb : d82162 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d7747, d82162, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7747, d82162, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d7748 q = 1) (hb : d82163 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d7748, d82163, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7748, d82163, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d82164 q = 1) (hb : d99279 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d82164, d99279, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d82164, d99279, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
  exact h8 p ha hb
theorem andIntro18261 (p : Pattern) (ha : d82174 p = 1) (hb : d99290 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d7013 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d99285 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d82170 q = 1) (hb : d99286 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d82170, d99286, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d82170, d99286, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d6380 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d82171 q = 1) (hb : d99287 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d82171, d99287, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d82171, d99287, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d82172 q = 1) (hb : d99288 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d82172, d99288, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d82172, d99288, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d82173 q = 1) (hb : d99289 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d82173, d99289, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d82173, d99289, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d82174 q = 1) (hb : d99290 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d82174, d99290, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d82174, d99290, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro18262 (p : Pattern) (ha : d82180 p = 1) (hb : d99296 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1181 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d7750 q = 1) (hb : d82158 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d7750, d82158, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18258 q ha hb
    | true =>
      simp only [d7750, d82158, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18259 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d6988 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d7751 q = 1) (hb : d82159 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d7751, d82159, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d7751, d82159, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d82160 q = 1) (hb : d99277 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d82160, d99277, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d82160, d99277, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d82161 q = 1) (hb : d99278 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d82161, d99278, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d82161, d99278, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d82165 q = 1) (hb : d99280 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d82165, d99280, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d82165, d99280, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18260 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d1371 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d82166 q = 1) (hb : d99281 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d82166, d99281, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d82166, d99281, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d82167 q = 1) (hb : d99282 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d82167, d99282, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d82167, d99282, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h11 (q : Pattern) (ha : d82168 q = 1) (hb : d99283 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d82168, d99283, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d82168, d99283, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h12 (q : Pattern) (ha : d82169 q = 1) (hb : d99284 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d82169, d99284, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d82169, d99284, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d82175 q = 1) (hb : d99291 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d82175, d99291, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d82175, d99291, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18261 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d1504 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d82176 q = 1) (hb : d99292 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d82176, d99292, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d82176, d99292, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d82177 q = 1) (hb : d99293 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d82177, d99293, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d82177, d99293, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h17 (q : Pattern) (ha : d82178 q = 1) (hb : d99294 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d82178, d99294, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d82178, d99294, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h18 (q : Pattern) (ha : d82179 q = 1) (hb : d99295 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d82179, d99295, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d82179, d99295, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h19 (q : Pattern) (ha : d82180 q = 1) (hb : d99296 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d82180, d99296, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d82180, d99296, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro18263 (p : Pattern) (ha : d82186 p = 1) (hb : d99302 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d82181 q = 1) (hb : d99297 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d82181, d99297, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d82181, d99297, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18262 q ha hb
  have h2 (q : Pattern) (ha : d82182 q = 1) (hb : d99298 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d82182, d99298, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d82182, d99298, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d82183 q = 1) (hb : d99299 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d82183, d99299, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d82183, d99299, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d82184 q = 1) (hb : d99300 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d82184, d99300, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d82184, d99300, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d82185 q = 1) (hb : d99301 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d82185, d99301, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d82185, d99301, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d82186 q = 1) (hb : d99302 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d82186, d99302, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d82186, d99302, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro18264 (p : Pattern) (ha : d7894 p = 1) (hb : d82194 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1650 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d1659 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d7047 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d7889 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d7890 q = 1) (hb : d82190 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d7890, d82190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d7890, d82190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d6446 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d7891 q = 1) (hb : d82191 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d7891, d82191, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d7891, d82191, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d7892 q = 1) (hb : d82192 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d7892, d82192, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d7892, d82192, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d7893 q = 1) (hb : d82193 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d7893, d82193, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d7893, d82193, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d7894 q = 1) (hb : d82194 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d7894, d82194, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7894, d82194, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro18265 (p : Pattern) (ha : d7903 p = 1) (hb : d82199 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1650 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1659 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d7047 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d7889 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d7890 q = 1) (hb : d82190 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d7890, d82190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d7890, d82190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d6446 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d7891 q = 1) (hb : d82191 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d7891, d82191, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d7891, d82191, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d7892 q = 1) (hb : d82192 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d7892, d82192, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d7892, d82192, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d7893 q = 1) (hb : d82193 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d7893, d82193, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7893, d82193, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d1808 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d1813 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d7055 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d7898 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d7899 q = 1) (hb : d82195 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d7899, d82195, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d7899, d82195, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d6467 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d7900 q = 1) (hb : d82196 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d7900, d82196, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d7900, d82196, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d7901 q = 1) (hb : d82197 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d7901, d82197, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d7901, d82197, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d7902 q = 1) (hb : d82198 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d7902, d82198, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d7902, d82198, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d7903 q = 1) (hb : d82199 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d7903, d82199, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d7903, d82199, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro18266 (p : Pattern) (ha : d82206 p = 1) (hb : d99308 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d7055 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d7898 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d7899 q = 1) (hb : d82195 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d7899, d82195, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d7899, d82195, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d6467 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d7900 q = 1) (hb : d82196 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d7900, d82196, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d7900, d82196, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d7901 q = 1) (hb : d82204 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d7901, d82204, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7901, d82204, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d7902 q = 1) (hb : d82205 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d7902, d82205, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7902, d82205, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d82206 q = 1) (hb : d99308 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d82206, d99308, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d82206, d99308, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
  exact h8 p ha hb
theorem andIntro18267 (p : Pattern) (ha : d82216 p = 1) (hb : d99319 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d7093 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d99314 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d82212 q = 1) (hb : d99315 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d82212, d99315, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d82212, d99315, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d6526 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d82213 q = 1) (hb : d99316 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d82213, d99316, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d82213, d99316, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d82214 q = 1) (hb : d99317 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d82214, d99317, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d82214, d99317, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d82215 q = 1) (hb : d99318 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d82215, d99318, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d82215, d99318, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d82216 q = 1) (hb : d99319 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d82216, d99319, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d82216, d99319, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro18268 (p : Pattern) (ha : d82222 p = 1) (hb : d99325 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1642 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d7904 q = 1) (hb : d82200 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d7904, d82200, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18264 q ha hb
    | true =>
      simp only [d7904, d82200, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18265 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d7068 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d7905 q = 1) (hb : d82201 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d7905, d82201, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d7905, d82201, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d82202 q = 1) (hb : d99306 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d82202, d99306, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d82202, d99306, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d82203 q = 1) (hb : d99307 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d82203, d99307, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d82203, d99307, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d82207 q = 1) (hb : d99309 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d82207, d99309, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d82207, d99309, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18266 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d1848 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d82208 q = 1) (hb : d99310 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d82208, d99310, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d82208, d99310, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d82209 q = 1) (hb : d99311 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d82209, d99311, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d82209, d99311, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h11 (q : Pattern) (ha : d82210 q = 1) (hb : d99312 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d82210, d99312, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d82210, d99312, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h12 (q : Pattern) (ha : d82211 q = 1) (hb : d99313 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d82211, d99313, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d82211, d99313, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d82217 q = 1) (hb : d99320 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d82217, d99320, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d82217, d99320, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18267 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d1981 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d82218 q = 1) (hb : d99321 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d82218, d99321, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d82218, d99321, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d82219 q = 1) (hb : d99322 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d82219, d99322, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d82219, d99322, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h17 (q : Pattern) (ha : d82220 q = 1) (hb : d99323 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d82220, d99323, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d82220, d99323, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h18 (q : Pattern) (ha : d82221 q = 1) (hb : d99324 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d82221, d99324, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d82221, d99324, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h19 (q : Pattern) (ha : d82222 q = 1) (hb : d99325 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d82222, d99325, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d82222, d99325, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro18269 (p : Pattern) (ha : d82228 p = 1) (hb : d99331 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d82223 q = 1) (hb : d99326 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d82223, d99326, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d82223, d99326, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18268 q ha hb
  have h2 (q : Pattern) (ha : d82224 q = 1) (hb : d99327 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d82224, d99327, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d82224, d99327, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d82225 q = 1) (hb : d99328 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d82225, d99328, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d82225, d99328, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d82226 q = 1) (hb : d99329 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d82226, d99329, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d82226, d99329, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d82227 q = 1) (hb : d99330 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d82227, d99330, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d82227, d99330, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d82228 q = 1) (hb : d99331 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d82228, d99331, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d82228, d99331, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro18270 (p : Pattern) (ha : d8049 p = 1) (hb : d82237 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d2133 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d2142 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d7128 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d8044 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d8045 q = 1) (hb : d82233 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d8045, d82233, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d8045, d82233, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d6593 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d8046 q = 1) (hb : d82234 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d8046, d82234, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d8046, d82234, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d8047 q = 1) (hb : d82235 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d8047, d82235, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d8047, d82235, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d8048 q = 1) (hb : d82236 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d8048, d82236, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d8048, d82236, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d8049 q = 1) (hb : d82237 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d8049, d82237, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8049, d82237, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro18271 (p : Pattern) (ha : d8058 p = 1) (hb : d82242 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d2133 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d2142 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d7128 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d8044 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d8045 q = 1) (hb : d82233 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d8045, d82233, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d8045, d82233, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d6593 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d8046 q = 1) (hb : d82234 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d8046, d82234, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d8046, d82234, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d8047 q = 1) (hb : d82235 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d8047, d82235, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d8047, d82235, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d8048 q = 1) (hb : d82236 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d8048, d82236, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8048, d82236, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d2286 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d2291 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d7136 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d8053 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d8054 q = 1) (hb : d82238 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d8054, d82238, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d8054, d82238, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d6614 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d8055 q = 1) (hb : d82239 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d8055, d82239, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d8055, d82239, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d8056 q = 1) (hb : d82240 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d8056, d82240, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d8056, d82240, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d8057 q = 1) (hb : d82241 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d8057, d82241, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d8057, d82241, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d8058 q = 1) (hb : d82242 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d8058, d82242, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d8058, d82242, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro18272 (p : Pattern) (ha : d82249 p = 1) (hb : d99338 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d7136 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d8053 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d8054 q = 1) (hb : d82238 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d8054, d82238, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d8054, d82238, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d6614 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d8055 q = 1) (hb : d82239 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d8055, d82239, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d8055, d82239, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d8056 q = 1) (hb : d82247 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d8056, d82247, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8056, d82247, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d8057 q = 1) (hb : d82248 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d8057, d82248, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8057, d82248, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d82249 q = 1) (hb : d99338 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d82249, d99338, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d82249, d99338, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
  exact h8 p ha hb
theorem andIntro18273 (p : Pattern) (ha : d82259 p = 1) (hb : d99349 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d7174 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d99344 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d82255 q = 1) (hb : d99345 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d82255, d99345, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d82255, d99345, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d6673 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d82256 q = 1) (hb : d99346 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d82256, d99346, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d82256, d99346, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d82257 q = 1) (hb : d99347 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d82257, d99347, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d82257, d99347, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d82258 q = 1) (hb : d99348 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d82258, d99348, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d82258, d99348, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d82259 q = 1) (hb : d99349 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d82259, d99349, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d82259, d99349, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro18274 (p : Pattern) (ha : d82265 p = 1) (hb : d99355 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d2125 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d8059 q = 1) (hb : d82243 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d8059, d82243, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18270 q ha hb
    | true =>
      simp only [d8059, d82243, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18271 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d7149 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d8060 q = 1) (hb : d82244 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d8060, d82244, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d8060, d82244, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d82245 q = 1) (hb : d99336 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d82245, d99336, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d82245, d99336, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d82246 q = 1) (hb : d99337 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d82246, d99337, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d82246, d99337, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d82250 q = 1) (hb : d99339 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d82250, d99339, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d82250, d99339, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18272 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d2326 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d82251 q = 1) (hb : d99340 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d82251, d99340, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d82251, d99340, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d82252 q = 1) (hb : d99341 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d82252, d99341, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d82252, d99341, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h11 (q : Pattern) (ha : d82253 q = 1) (hb : d99342 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d82253, d99342, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d82253, d99342, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h12 (q : Pattern) (ha : d82254 q = 1) (hb : d99343 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d82254, d99343, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d82254, d99343, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d82260 q = 1) (hb : d99350 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d82260, d99350, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d82260, d99350, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18273 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d2459 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d82261 q = 1) (hb : d99351 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d82261, d99351, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d82261, d99351, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d82262 q = 1) (hb : d99352 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d82262, d99352, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d82262, d99352, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h17 (q : Pattern) (ha : d82263 q = 1) (hb : d99353 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d82263, d99353, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d82263, d99353, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h18 (q : Pattern) (ha : d82264 q = 1) (hb : d99354 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d82264, d99354, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d82264, d99354, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h19 (q : Pattern) (ha : d82265 q = 1) (hb : d99355 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d82265, d99355, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d82265, d99355, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro18275 (p : Pattern) (ha : d82271 p = 1) (hb : d99361 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d82266 q = 1) (hb : d99356 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d82266, d99356, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d82266, d99356, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18274 q ha hb
  have h2 (q : Pattern) (ha : d82267 q = 1) (hb : d99357 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d82267, d99357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d82267, d99357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d82268 q = 1) (hb : d99358 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d82268, d99358, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d82268, d99358, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d82269 q = 1) (hb : d99359 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d82269, d99359, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d82269, d99359, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d82270 q = 1) (hb : d99360 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d82270, d99360, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d82270, d99360, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d82271 q = 1) (hb : d99361 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d82271, d99361, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d82271, d99361, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro18276 (p : Pattern) (ha : d82277 p = 1) (hb : d99367 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d82106 q = 1) (hb : d99248 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d82106, d99248, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18245 q ha hb
    | true =>
      simp only [d82106, d99248, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18251 q ha hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d82146 q = 1) (hb : d99275 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d82146, d99275, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d82146, d99275, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18257 q ha hb
  have h3 (q : Pattern) (ha : d82147 q = 1) (hb : d99276 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d82147, d99276, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d82147, d99276, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d82187 q = 1) (hb : d99303 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d82187, d99303, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d82187, d99303, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18263 q ha hb
  have h5 (q : Pattern) (ha : d82188 q = 1) (hb : d99304 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d82188, d99304, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d82188, d99304, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d82189 q = 1) (hb : d99305 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d82189, d99305, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d82189, d99305, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d82229 q = 1) (hb : d99332 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d82229, d99332, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d82229, d99332, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18269 q ha hb
  have h8 (q : Pattern) (ha : d82230 q = 1) (hb : d99333 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d82230, d99333, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d82230, d99333, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d82231 q = 1) (hb : d99334 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d82231, d99334, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d82231, d99334, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d82232 q = 1) (hb : d99335 q = 1) : d0 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d82232, d99335, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d82232, d99335, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d82272 q = 1) (hb : d99362 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d82272, d99362, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d82272, d99362, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18275 q ha hb
  have h12 (q : Pattern) (ha : d82273 q = 1) (hb : d99363 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d82273, d99363, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d82273, d99363, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d82274 q = 1) (hb : d99364 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d82274, d99364, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d82274, d99364, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d82275 q = 1) (hb : d99365 q = 1) : d0 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d82275, d99365, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d82275, d99365, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d82276 q = 1) (hb : d99366 q = 1) : d0 q = 1 := by
    cases bit : q 10250 with
    | false =>
      simp only [d82276, d99366, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d82276, d99366, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d82277 q = 1) (hb : d99367 q = 1) : d0 q = 1 := by
    cases bit : q 260 with
    | false =>
      simp only [d82277, d99367, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d82277, d99367, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  exact h16 p ha hb
theorem andIntro18277 (p : Pattern) (ha : d82283 p = 1) (hb : d99373 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d82278 q = 1) (hb : d99368 q = 1) : d0 q = 1 := by
    cases bit : q 259 with
    | false =>
      simp only [d82278, d99368, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18276 q ha hb
    | true =>
      simp only [d82278, d99368, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d82279 q = 1) (hb : d99369 q = 1) : d0 q = 1 := by
    cases bit : q 258 with
    | false =>
      simp only [d82279, d99369, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d82279, d99369, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d82280 q = 1) (hb : d99370 q = 1) : d0 q = 1 := by
    cases bit : q 257 with
    | false =>
      simp only [d82280, d99370, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d82280, d99370, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d82281 q = 1) (hb : d99371 q = 1) : d0 q = 1 := by
    cases bit : q 256 with
    | false =>
      simp only [d82281, d99371, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d82281, d99371, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d82282 q = 1) (hb : d99372 q = 1) : d0 q = 1 := by
    cases bit : q 255 with
    | false =>
      simp only [d82282, d99372, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d82282, d99372, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d82283 q = 1) (hb : d99373 q = 1) : d0 q = 1 := by
    cases bit : q 254 with
    | false =>
      simp only [d82283, d99373, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d82283, d99373, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro18278 (p : Pattern) (ha : d82289 p = 1) (hb : d99379 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d82284 q = 1) (hb : d99374 q = 1) : d0 q = 1 := by
    cases bit : q 253 with
    | false =>
      simp only [d82284, d99374, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18277 q ha hb
    | true =>
      simp only [d82284, d99374, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d82285 q = 1) (hb : d99375 q = 1) : d0 q = 1 := by
    cases bit : q 252 with
    | false =>
      simp only [d82285, d99375, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d82285, d99375, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d82286 q = 1) (hb : d99376 q = 1) : d0 q = 1 := by
    cases bit : q 251 with
    | false =>
      simp only [d82286, d99376, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d82286, d99376, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d82287 q = 1) (hb : d99377 q = 1) : d0 q = 1 := by
    cases bit : q 250 with
    | false =>
      simp only [d82287, d99377, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d82287, d99377, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d82288 q = 1) (hb : d99378 q = 1) : d0 q = 1 := by
    cases bit : q 249 with
    | false =>
      simp only [d82288, d99378, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d82288, d99378, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d82289 q = 1) (hb : d99379 q = 1) : d0 q = 1 := by
    cases bit : q 245 with
    | false =>
      simp only [d82289, d99379, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d82289, d99379, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro18279 (p : Pattern) (ha : d82295 p = 1) (hb : d99385 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d82290 q = 1) (hb : d99380 q = 1) : d0 q = 1 := by
    cases bit : q 200 with
    | false =>
      simp only [d82290, d99380, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18278 q ha hb
    | true =>
      simp only [d82290, d99380, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d82291 q = 1) (hb : d99381 q = 1) : d0 q = 1 := by
    cases bit : q 199 with
    | false =>
      simp only [d82291, d99381, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d82291, d99381, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d82292 q = 1) (hb : d99382 q = 1) : d0 q = 1 := by
    cases bit : q 186 with
    | false =>
      simp only [d82292, d99382, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d82292, d99382, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d82293 q = 1) (hb : d99383 q = 1) : d0 q = 1 := by
    cases bit : q 185 with
    | false =>
      simp only [d82293, d99383, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d82293, d99383, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d82294 q = 1) (hb : d99384 q = 1) : d0 q = 1 := by
    cases bit : q 184 with
    | false =>
      simp only [d82294, d99384, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d82294, d99384, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d82295 q = 1) (hb : d99385 q = 1) : d0 q = 1 := by
    cases bit : q 181 with
    | false =>
      simp only [d82295, d99385, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d82295, d99385, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro18280 (p : Pattern) (ha : d82301 p = 1) (hb : d99391 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d82296 q = 1) (hb : d99386 q = 1) : d0 q = 1 := by
    cases bit : q 177 with
    | false =>
      simp only [d82296, d99386, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18279 q ha hb
    | true =>
      simp only [d82296, d99386, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d82297 q = 1) (hb : d99387 q = 1) : d0 q = 1 := by
    cases bit : q 164 with
    | false =>
      simp only [d82297, d99387, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d82297, d99387, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d82298 q = 1) (hb : d99388 q = 1) : d0 q = 1 := by
    cases bit : q 156 with
    | false =>
      simp only [d82298, d99388, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d82298, d99388, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d82299 q = 1) (hb : d99389 q = 1) : d0 q = 1 := by
    cases bit : q 155 with
    | false =>
      simp only [d82299, d99389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d82299, d99389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d82300 q = 1) (hb : d99390 q = 1) : d0 q = 1 := by
    cases bit : q 134 with
    | false =>
      simp only [d82300, d99390, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d82300, d99390, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d82301 q = 1) (hb : d99391 q = 1) : d0 q = 1 := by
    cases bit : q 133 with
    | false =>
      simp only [d82301, d99391, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d82301, d99391, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro18281 (p : Pattern) (ha : d82307 p = 1) (hb : d99397 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d82302 q = 1) (hb : d99392 q = 1) : d0 q = 1 := by
    cases bit : q 120 with
    | false =>
      simp only [d82302, d99392, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18280 q ha hb
    | true =>
      simp only [d82302, d99392, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d82303 q = 1) (hb : d99393 q = 1) : d0 q = 1 := by
    cases bit : q 118 with
    | false =>
      simp only [d82303, d99393, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d82303, d99393, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d82304 q = 1) (hb : d99394 q = 1) : d0 q = 1 := by
    cases bit : q 114 with
    | false =>
      simp only [d82304, d99394, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d82304, d99394, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d82305 q = 1) (hb : d99395 q = 1) : d0 q = 1 := by
    cases bit : q 111 with
    | false =>
      simp only [d82305, d99395, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d82305, d99395, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d82306 q = 1) (hb : d99396 q = 1) : d0 q = 1 := by
    cases bit : q 98 with
    | false =>
      simp only [d82306, d99396, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d82306, d99396, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d82307 q = 1) (hb : d99397 q = 1) : d0 q = 1 := by
    cases bit : q 97 with
    | false =>
      simp only [d82307, d99397, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d82307, d99397, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro18282 (p : Pattern) (ha : d82313 p = 1) (hb : d99403 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d82308 q = 1) (hb : d99398 q = 1) : d0 q = 1 := by
    cases bit : q 94 with
    | false =>
      simp only [d82308, d99398, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18281 q ha hb
    | true =>
      simp only [d82308, d99398, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d82309 q = 1) (hb : d99399 q = 1) : d0 q = 1 := by
    cases bit : q 76 with
    | false =>
      simp only [d82309, d99399, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d82309, d99399, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d82310 q = 1) (hb : d99400 q = 1) : d0 q = 1 := by
    cases bit : q 67 with
    | false =>
      simp only [d82310, d99400, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d82310, d99400, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d82311 q = 1) (hb : d99401 q = 1) : d0 q = 1 := by
    cases bit : q 52 with
    | false =>
      simp only [d82311, d99401, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d82311, d99401, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d82312 q = 1) (hb : d99402 q = 1) : d0 q = 1 := by
    cases bit : q 47 with
    | false =>
      simp only [d82312, d99402, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d82312, d99402, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d82313 q = 1) (hb : d99403 q = 1) : d0 q = 1 := by
    cases bit : q 46 with
    | false =>
      simp only [d82313, d99403, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d82313, d99403, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro18283 (p : Pattern) (ha : d82319 p = 1) (hb : d99409 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d82314 q = 1) (hb : d99404 q = 1) : d0 q = 1 := by
    cases bit : q 45 with
    | false =>
      simp only [d82314, d99404, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18282 q ha hb
    | true =>
      simp only [d82314, d99404, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d82315 q = 1) (hb : d99405 q = 1) : d0 q = 1 := by
    cases bit : q 30 with
    | false =>
      simp only [d82315, d99405, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d82315, d99405, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d82316 q = 1) (hb : d99406 q = 1) : d0 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d82316, d99406, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d82316, d99406, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d82317 q = 1) (hb : d99407 q = 1) : d0 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d82317, d99407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d82317, d99407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d82318 q = 1) (hb : d99408 q = 1) : d0 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d82318, d99408, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d82318, d99408, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d82319 q = 1) (hb : d99409 q = 1) : d0 q = 1 := by
    cases bit : q 25 with
    | false =>
      simp only [d82319, d99409, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d82319, d99409, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro18284 (p : Pattern) (ha : d7241 p = 1) (hb : d112688 p = 1) : d114101 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d94753 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d30 q = 1) (hb : d94753 q = 1) : d30 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d145 q = 1) (hb : d94753 q = 1) : d4819 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d145, d4819, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12423 q ha hb
    | true =>
      simp only [d145, d4819, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d146 q = 1) (hb : d94753 q = 1) : d4820 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d146, d4820, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d146, d4820, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d147 q = 1) (hb : d94753 q = 1) : d4821 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d147, d4821, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d147, d4821, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d33 q = 1) (hb : d112686 q = 1) : d33 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d148 q = 1) (hb : d112687 q = 1) : d12225 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d148, d112687, d12225, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d148, d112687, d12225, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d7240 q = 1) (hb : d112688 q = 1) : d114100 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d7240, d112688, d114100, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d7240, d112688, d114100, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d112688 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d7241 q = 1) (hb : d112688 q = 1) : d114101 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d7241, d114101, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d7241, d114101, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro18285 (p : Pattern) (ha : d7247 p = 1) (hb : d112688 p = 1) : d114107 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d112688 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d7242 q = 1) (hb : d112688 q = 1) : d114102 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d7242, d114102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18284 q ha hb
    | true =>
      simp only [d7242, d114102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d7243 q = 1) (hb : d112688 q = 1) : d114103 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d7243, d114103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7243, d114103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d38 q = 1) (hb : d112688 q = 1) : d38 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d7244 q = 1) (hb : d112688 q = 1) : d114104 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d7244, d114104, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d7244, d114104, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d7245 q = 1) (hb : d112688 q = 1) : d114105 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d7245, d114105, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d7245, d114105, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d7246 q = 1) (hb : d112688 q = 1) : d114106 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d7246, d114106, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d7246, d114106, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d7247 q = 1) (hb : d112688 q = 1) : d114107 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d7247, d114107, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7247, d114107, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro18286 (p : Pattern) (ha : d85394 p = 1) (hb : d112688 p = 1) : d114113 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d112688 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d120 q = 1) (hb : d112688 q = 1) : d120 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d126 q = 1) (hb : d112688 q = 1) : d126 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d42 q = 1) (hb : d112688 q = 1) : d42 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d7248 q = 1) (hb : d112688 q = 1) : d114108 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7248, d114108, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18285 q ha hb
    | true =>
      simp only [d7248, d114108, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d85390 q = 1) (hb : d112688 q = 1) : d114109 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d85390, d114109, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d85390, d114109, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d44 q = 1) (hb : d112688 q = 1) : d44 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d85391 q = 1) (hb : d112688 q = 1) : d114110 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d85391, d114110, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d85391, d114110, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d85392 q = 1) (hb : d112688 q = 1) : d114111 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d85392, d114111, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d85392, d114111, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d85393 q = 1) (hb : d112688 q = 1) : d114112 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d85393, d114112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d85393, d114112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d85394 q = 1) (hb : d112688 q = 1) : d114113 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d85394, d114113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d85394, d114113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro18287 (p : Pattern) (ha : d7254 p = 1) (hb : d112688 p = 1) : d114114 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d112688 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d7242 q = 1) (hb : d112688 q = 1) : d114102 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d7242, d114102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18284 q ha hb
    | true =>
      simp only [d7242, d114102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d7243 q = 1) (hb : d112688 q = 1) : d114103 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d7243, d114103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7243, d114103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d38 q = 1) (hb : d112688 q = 1) : d38 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d7244 q = 1) (hb : d112688 q = 1) : d114104 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d7244, d114104, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d7244, d114104, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d7245 q = 1) (hb : d112688 q = 1) : d114105 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d7245, d114105, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d7245, d114105, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d7246 q = 1) (hb : d112688 q = 1) : d114106 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d7246, d114106, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d7246, d114106, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d7254 q = 1) (hb : d112688 q = 1) : d114114 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d7254, d114114, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d7254, d114114, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h7 p ha hb
theorem andIntro18288 (p : Pattern) (ha : d85399 p = 1) (hb : d112688 p = 1) : d114120 p = 1 := by
  have h0 (q : Pattern) (ha : d120 q = 1) (hb : d112688 q = 1) : d120 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d126 q = 1) (hb : d112688 q = 1) : d126 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d42 q = 1) (hb : d112688 q = 1) : d42 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d7248 q = 1) (hb : d112688 q = 1) : d114108 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7248, d114108, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18285 q ha hb
    | true =>
      simp only [d7248, d114108, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d112688 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d85390 q = 1) (hb : d112688 q = 1) : d114109 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d85390, d114109, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d85390, d114109, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d44 q = 1) (hb : d112688 q = 1) : d44 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d85391 q = 1) (hb : d112688 q = 1) : d114110 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d85391, d114110, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d85391, d114110, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d85392 q = 1) (hb : d112688 q = 1) : d114111 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d85392, d114111, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d85392, d114111, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d85393 q = 1) (hb : d112688 q = 1) : d114112 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d85393, d114112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d85393, d114112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d198 q = 1) (hb : d112688 q = 1) : d198 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d202 q = 1) (hb : d112688 q = 1) : d202 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d49 q = 1) (hb : d112688 q = 1) : d49 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d7255 q = 1) (hb : d112688 q = 1) : d114115 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7255, d114115, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18287 q ha hb
    | true =>
      simp only [d7255, d114115, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d85395 q = 1) (hb : d112688 q = 1) : d114116 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d85395, d114116, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d85395, d114116, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h15 (q : Pattern) (ha : d51 q = 1) (hb : d112688 q = 1) : d51 q = 1 := by
    exact ha
  have h16 (q : Pattern) (ha : d85396 q = 1) (hb : d112688 q = 1) : d114117 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d85396, d114117, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d85396, d114117, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d85397 q = 1) (hb : d112688 q = 1) : d114118 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d85397, d114118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d85397, d114118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d85398 q = 1) (hb : d112688 q = 1) : d114119 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d85398, d114119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d85398, d114119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d85399 q = 1) (hb : d112688 q = 1) : d114120 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d85399, d114120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d85399, d114120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro18289 (p : Pattern) (ha : d85406 p = 1) (hb : d112688 p = 1) : d114127 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d112688 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d49 q = 1) (hb : d112688 q = 1) : d49 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d7255 q = 1) (hb : d112688 q = 1) : d114115 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7255, d114115, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18287 q ha hb
    | true =>
      simp only [d7255, d114115, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d85395 q = 1) (hb : d112688 q = 1) : d114116 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d85395, d114116, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d85395, d114116, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d51 q = 1) (hb : d112688 q = 1) : d51 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d85396 q = 1) (hb : d112688 q = 1) : d114117 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d85396, d114117, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d85396, d114117, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d85404 q = 1) (hb : d112688 q = 1) : d114125 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d85404, d114125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d85404, d114125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d85405 q = 1) (hb : d112688 q = 1) : d114126 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d85405, d114126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d85405, d114126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d85406 q = 1) (hb : d112688 q = 1) : d114127 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d85406, d114127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d85406, d114127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro18290 (p : Pattern) (ha : d7274 p = 1) (hb : d112688 p = 1) : d114134 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d94753 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d71 q = 1) (hb : d94753 q = 1) : d71 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d232 q = 1) (hb : d94753 q = 1) : d6079 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d232, d6079, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12435 q ha hb
    | true =>
      simp only [d232, d6079, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d233 q = 1) (hb : d94753 q = 1) : d6080 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d233, d6080, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d233, d6080, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d234 q = 1) (hb : d94753 q = 1) : d6081 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d234, d6081, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d234, d6081, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d74 q = 1) (hb : d112686 q = 1) : d74 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d235 q = 1) (hb : d112687 q = 1) : d12259 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d235, d112687, d12259, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d235, d112687, d12259, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d7273 q = 1) (hb : d112688 q = 1) : d114133 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d7273, d112688, d114133, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d7273, d112688, d114133, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d112688 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d7274 q = 1) (hb : d112688 q = 1) : d114134 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d7274, d114134, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d7274, d114134, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro18291 (p : Pattern) (ha : d7280 p = 1) (hb : d112688 p = 1) : d114140 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d112688 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d7275 q = 1) (hb : d112688 q = 1) : d114135 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d7275, d114135, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18290 q ha hb
    | true =>
      simp only [d7275, d114135, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d7276 q = 1) (hb : d112688 q = 1) : d114136 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d7276, d114136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7276, d114136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d79 q = 1) (hb : d112688 q = 1) : d79 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d7277 q = 1) (hb : d112688 q = 1) : d114137 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d7277, d114137, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d7277, d114137, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d7278 q = 1) (hb : d112688 q = 1) : d114138 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d7278, d114138, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d7278, d114138, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d7279 q = 1) (hb : d112688 q = 1) : d114139 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d7279, d114139, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d7279, d114139, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d7280 q = 1) (hb : d112688 q = 1) : d114140 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d7280, d114140, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d7280, d114140, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h7 p ha hb
theorem andIntro18292 (p : Pattern) (ha : d85416 p = 1) (hb : d112688 p = 1) : d114146 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d112688 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d83 q = 1) (hb : d112688 q = 1) : d83 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d7281 q = 1) (hb : d112688 q = 1) : d114141 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7281, d114141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18291 q ha hb
    | true =>
      simp only [d7281, d114141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d85412 q = 1) (hb : d112688 q = 1) : d114142 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d85412, d114142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d85412, d114142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d85 q = 1) (hb : d112688 q = 1) : d85 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d85413 q = 1) (hb : d112688 q = 1) : d114143 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d85413, d114143, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d85413, d114143, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d85414 q = 1) (hb : d112688 q = 1) : d114144 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d85414, d114144, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d85414, d114144, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d85415 q = 1) (hb : d112688 q = 1) : d114145 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d85415, d114145, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d85415, d114145, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d85416 q = 1) (hb : d112688 q = 1) : d114146 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d85416, d114146, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d85416, d114146, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro18293 (p : Pattern) (ha : d85422 p = 1) (hb : d112688 p = 1) : d114152 p = 1 := by
  have h0 (q : Pattern) (ha : d114 q = 1) (hb : d112688 q = 1) : d114 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d85400 q = 1) (hb : d112688 q = 1) : d114121 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d85400, d114121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18286 q ha hb
    | true =>
      simp only [d85400, d114121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18288 q ha hb
  have h2 (q : Pattern) (ha : d214 q = 1) (hb : d112688 q = 1) : d214 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d85401 q = 1) (hb : d112688 q = 1) : d114122 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d85401, d114122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d85401, d114122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d112688 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d85402 q = 1) (hb : d112688 q = 1) : d114123 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d85402, d114123, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d85402, d114123, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d85403 q = 1) (hb : d112688 q = 1) : d114124 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d85403, d114124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d85403, d114124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d85407 q = 1) (hb : d112688 q = 1) : d114128 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d85407, d114128, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d85407, d114128, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18289 q ha hb
  have h8 (q : Pattern) (ha : d85408 q = 1) (hb : d112688 q = 1) : d114129 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d85408, d114129, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d85408, d114129, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h9 (q : Pattern) (ha : d85409 q = 1) (hb : d112688 q = 1) : d114130 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d85409, d114130, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d85409, d114130, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h10 (q : Pattern) (ha : d85410 q = 1) (hb : d112688 q = 1) : d114131 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d85410, d114131, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d85410, d114131, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h11 (q : Pattern) (ha : d85411 q = 1) (hb : d112688 q = 1) : d114132 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d85411, d114132, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d85411, d114132, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d85417 q = 1) (hb : d112688 q = 1) : d114147 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d85417, d114147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d85417, d114147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18292 q ha hb
  have h13 (q : Pattern) (ha : d85418 q = 1) (hb : d112688 q = 1) : d114148 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d85418, d114148, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d85418, d114148, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h14 (q : Pattern) (ha : d85419 q = 1) (hb : d112688 q = 1) : d114149 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d85419, d114149, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d85419, d114149, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h15 (q : Pattern) (ha : d85420 q = 1) (hb : d112688 q = 1) : d114150 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d85420, d114150, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d85420, d114150, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h16 (q : Pattern) (ha : d85421 q = 1) (hb : d112688 q = 1) : d114151 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d85421, d114151, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d85421, d114151, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h17 (q : Pattern) (ha : d85422 q = 1) (hb : d112688 q = 1) : d114152 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d85422, d114152, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d85422, d114152, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  exact h17 p ha hb
theorem andIntro18294 (p : Pattern) (ha : d7302 p = 1) (hb : d112688 p = 1) : d114162 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d112688 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d42 q = 1) (hb : d112688 q = 1) : d42 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d7248 q = 1) (hb : d112688 q = 1) : d114108 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7248, d114108, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18285 q ha hb
    | true =>
      simp only [d7248, d114108, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d7298 q = 1) (hb : d112688 q = 1) : d114158 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d7298, d114158, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7298, d114158, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d7299 q = 1) (hb : d112688 q = 1) : d114159 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d7299, d114159, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d7299, d114159, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d7300 q = 1) (hb : d112688 q = 1) : d114160 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d7300, d114160, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7300, d114160, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d7301 q = 1) (hb : d112688 q = 1) : d114161 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d7301, d114161, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7301, d114161, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d7302 q = 1) (hb : d112688 q = 1) : d114162 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d7302, d114162, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7302, d114162, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro18295 (p : Pattern) (ha : d7309 p = 1) (hb : d112688 p = 1) : d114169 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d112688 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d42 q = 1) (hb : d112688 q = 1) : d42 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d7248 q = 1) (hb : d112688 q = 1) : d114108 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7248, d114108, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18285 q ha hb
    | true =>
      simp only [d7248, d114108, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d7298 q = 1) (hb : d112688 q = 1) : d114158 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d7298, d114158, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7298, d114158, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d7299 q = 1) (hb : d112688 q = 1) : d114159 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d7299, d114159, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d7299, d114159, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d7300 q = 1) (hb : d112688 q = 1) : d114160 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d7300, d114160, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7300, d114160, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d7301 q = 1) (hb : d112688 q = 1) : d114161 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d7301, d114161, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7301, d114161, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d49 q = 1) (hb : d112688 q = 1) : d49 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d7255 q = 1) (hb : d112688 q = 1) : d114115 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7255, d114115, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18287 q ha hb
    | true =>
      simp only [d7255, d114115, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d7305 q = 1) (hb : d112688 q = 1) : d114165 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d7305, d114165, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7305, d114165, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d7306 q = 1) (hb : d112688 q = 1) : d114166 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d7306, d114166, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d7306, d114166, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d7307 q = 1) (hb : d112688 q = 1) : d114167 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d7307, d114167, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7307, d114167, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d7308 q = 1) (hb : d112688 q = 1) : d114168 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d7308, d114168, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7308, d114168, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d7309 q = 1) (hb : d112688 q = 1) : d114169 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d7309, d114169, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d7309, d114169, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  exact h13 p ha hb
theorem andIntro18296 (p : Pattern) (ha : d7376 p = 1) (hb : d112688 p = 1) : d114226 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d112688 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d42 q = 1) (hb : d112688 q = 1) : d42 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d7248 q = 1) (hb : d112688 q = 1) : d114108 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7248, d114108, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18285 q ha hb
    | true =>
      simp only [d7248, d114108, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d7298 q = 1) (hb : d112688 q = 1) : d114158 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d7298, d114158, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7298, d114158, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d7299 q = 1) (hb : d112688 q = 1) : d114159 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d7299, d114159, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d7299, d114159, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d7300 q = 1) (hb : d112688 q = 1) : d114160 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d7300, d114160, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7300, d114160, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d7301 q = 1) (hb : d112688 q = 1) : d114161 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d7301, d114161, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7301, d114161, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d103 q = 1) (hb : d112688 q = 1) : d103 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d7376 q = 1) (hb : d112688 q = 1) : d114226 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d7376, d114226, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d7376, d114226, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro18297 (p : Pattern) (ha : d7314 p = 1) (hb : d112688 p = 1) : d114174 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d112688 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d7242 q = 1) (hb : d112688 q = 1) : d114102 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d7242, d114102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18284 q ha hb
    | true =>
      simp only [d7242, d114102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d7243 q = 1) (hb : d112688 q = 1) : d114103 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d7243, d114103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7243, d114103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d38 q = 1) (hb : d112688 q = 1) : d38 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d7244 q = 1) (hb : d112688 q = 1) : d114104 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d7244, d114104, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d7244, d114104, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d7245 q = 1) (hb : d112688 q = 1) : d114105 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d7245, d114105, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d7245, d114105, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d7313 q = 1) (hb : d112688 q = 1) : d114173 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d7313, d114173, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7313, d114173, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d7314 q = 1) (hb : d112688 q = 1) : d114174 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d7314, d114174, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7314, d114174, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro18298 (p : Pattern) (ha : d7321 p = 1) (hb : d112688 p = 1) : d114181 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d112688 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d7242 q = 1) (hb : d112688 q = 1) : d114102 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d7242, d114102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18284 q ha hb
    | true =>
      simp only [d7242, d114102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d7243 q = 1) (hb : d112688 q = 1) : d114103 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d7243, d114103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7243, d114103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d38 q = 1) (hb : d112688 q = 1) : d38 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d7244 q = 1) (hb : d112688 q = 1) : d114104 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d7244, d114104, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d7244, d114104, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d7319 q = 1) (hb : d112688 q = 1) : d114179 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d7319, d114179, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7319, d114179, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d7320 q = 1) (hb : d112688 q = 1) : d114180 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d7320, d114180, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d7320, d114180, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d7321 q = 1) (hb : d112688 q = 1) : d114181 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d7321, d114181, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7321, d114181, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro18299 (p : Pattern) (ha : d7326 p = 1) (hb : d112688 p = 1) : d114187 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d94753 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d325 q = 1) (hb : d94753 q = 1) : d12313 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d325, d12313, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12463 q ha hb
    | true =>
      simp only [d325, d12313, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12423 q ha hb
  have h2 (q : Pattern) (ha : d326 q = 1) (hb : d94753 q = 1) : d12314 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d326, d12314, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d326, d12314, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d327 q = 1) (hb : d94753 q = 1) : d12315 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d327, d12315, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d327, d12315, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d112686 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d30 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d145 q = 1) (hb : d112686 q = 1) : d88338 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d145, d112686, d88338, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12423 q ha hb
    | true =>
      simp only [d145, d112686, d88338, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d146 q = 1) (hb : d112686 q = 1) : d88339 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d146, d88339, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d146, d88339, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d147 q = 1) (hb : d112686 q = 1) : d88340 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d147, d88340, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d147, d88340, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d328 q = 1) (hb : d112687 q = 1) : d114185 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d328, d112687, d114185, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d328, d112687, d114185, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d7325 q = 1) (hb : d112688 q = 1) : d114186 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d7325, d112688, d114186, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d7325, d112688, d114186, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d112688 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d7326 q = 1) (hb : d112688 q = 1) : d114187 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d7326, d114187, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d7326, d114187, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  exact h13 p ha hb
theorem andIntro18300 (p : Pattern) (ha : d7332 p = 1) (hb : d112688 p = 1) : d114193 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d112688 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d7327 q = 1) (hb : d112688 q = 1) : d114188 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d7327, d114188, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18299 q ha hb
    | true =>
      simp only [d7327, d114188, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d7328 q = 1) (hb : d112688 q = 1) : d114189 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d7328, d114189, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7328, d114189, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d7242 q = 1) (hb : d112688 q = 1) : d114102 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d7242, d114102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18284 q ha hb
    | true =>
      simp only [d7242, d114102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d7243 q = 1) (hb : d112688 q = 1) : d114103 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d7243, d114103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7243, d114103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d7329 q = 1) (hb : d112688 q = 1) : d114190 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d7329, d114190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d7329, d114190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d7330 q = 1) (hb : d112688 q = 1) : d114191 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d7330, d114191, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d7330, d114191, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d7331 q = 1) (hb : d112688 q = 1) : d114192 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d7331, d114192, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d7331, d114192, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d7332 q = 1) (hb : d112688 q = 1) : d114193 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d7332, d114193, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7332, d114193, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro18301 (p : Pattern) (ha : d7347 p = 1) (hb : d112688 p = 1) : d114199 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d112688 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d7242 q = 1) (hb : d112688 q = 1) : d114102 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d7242, d114102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18284 q ha hb
    | true =>
      simp only [d7242, d114102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d7243 q = 1) (hb : d112688 q = 1) : d114103 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d7243, d114103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7243, d114103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d7344 q = 1) (hb : d112688 q = 1) : d114196 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d7344, d114196, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d7344, d114196, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d7345 q = 1) (hb : d112688 q = 1) : d114197 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d7345, d114197, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d7345, d114197, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d7346 q = 1) (hb : d112688 q = 1) : d114198 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d7346, d114198, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d7346, d114198, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d7347 q = 1) (hb : d112688 q = 1) : d114199 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d7347, d114199, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7347, d114199, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro18302 (p : Pattern) (ha : d85432 p = 1) (hb : d112688 p = 1) : d114205 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d112688 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d116 q = 1) (hb : d112688 q = 1) : d116 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d7315 q = 1) (hb : d112688 q = 1) : d114175 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7315, d114175, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18297 q ha hb
    | true =>
      simp only [d7315, d114175, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d7316 q = 1) (hb : d112688 q = 1) : d114176 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d7316, d114176, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7316, d114176, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d7317 q = 1) (hb : d112688 q = 1) : d114177 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d7317, d114177, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d7317, d114177, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d7318 q = 1) (hb : d112688 q = 1) : d114178 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d7318, d114178, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7318, d114178, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d123 q = 1) (hb : d112688 q = 1) : d123 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d7322 q = 1) (hb : d112688 q = 1) : d114182 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7322, d114182, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18298 q ha hb
    | true =>
      simp only [d7322, d114182, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d7323 q = 1) (hb : d112688 q = 1) : d114183 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d7323, d114183, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7323, d114183, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d7324 q = 1) (hb : d112688 q = 1) : d114184 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d7324, d114184, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d7324, d114184, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d7333 q = 1) (hb : d112688 q = 1) : d114194 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7333, d114194, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18300 q ha hb
    | true =>
      simp only [d7333, d114194, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18285 q ha hb
  have h11 (q : Pattern) (ha : d85428 q = 1) (hb : d112688 q = 1) : d114195 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d85428, d114195, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d85428, d114195, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d7348 q = 1) (hb : d112688 q = 1) : d114200 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7348, d114200, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18301 q ha hb
    | true =>
      simp only [d7348, d114200, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d7349 q = 1) (hb : d112688 q = 1) : d114201 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d7349, d114201, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d7349, d114201, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d85429 q = 1) (hb : d112688 q = 1) : d114202 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d85429, d114202, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d85429, d114202, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d85430 q = 1) (hb : d112688 q = 1) : d114203 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d85430, d114203, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d85430, d114203, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d85431 q = 1) (hb : d112688 q = 1) : d114204 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d85431, d114204, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d85431, d114204, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d85432 q = 1) (hb : d112688 q = 1) : d114205 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d85432, d114205, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d85432, d114205, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  exact h17 p ha hb
theorem andIntro18303 (p : Pattern) (ha : d7354 p = 1) (hb : d112688 p = 1) : d114206 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d112688 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d7242 q = 1) (hb : d112688 q = 1) : d114102 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d7242, d114102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18284 q ha hb
    | true =>
      simp only [d7242, d114102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d7243 q = 1) (hb : d112688 q = 1) : d114103 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d7243, d114103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7243, d114103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d38 q = 1) (hb : d112688 q = 1) : d38 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d7244 q = 1) (hb : d112688 q = 1) : d114104 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d7244, d114104, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d7244, d114104, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d7245 q = 1) (hb : d112688 q = 1) : d114105 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d7245, d114105, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d7245, d114105, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d7313 q = 1) (hb : d112688 q = 1) : d114173 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d7313, d114173, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7313, d114173, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d7354 q = 1) (hb : d112688 q = 1) : d114206 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d7354, d114206, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d7354, d114206, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h7 p ha hb
theorem andIntro18304 (p : Pattern) (ha : d7359 p = 1) (hb : d112688 p = 1) : d114211 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d112688 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d7242 q = 1) (hb : d112688 q = 1) : d114102 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d7242, d114102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18284 q ha hb
    | true =>
      simp only [d7242, d114102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d7243 q = 1) (hb : d112688 q = 1) : d114103 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d7243, d114103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7243, d114103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d38 q = 1) (hb : d112688 q = 1) : d38 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d7244 q = 1) (hb : d112688 q = 1) : d114104 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d7244, d114104, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d7244, d114104, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d7319 q = 1) (hb : d112688 q = 1) : d114179 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d7319, d114179, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7319, d114179, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d7320 q = 1) (hb : d112688 q = 1) : d114180 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d7320, d114180, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d7320, d114180, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d7359 q = 1) (hb : d112688 q = 1) : d114211 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d7359, d114211, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d7359, d114211, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h7 p ha hb
theorem andIntro18305 (p : Pattern) (ha : d7363 p = 1) (hb : d112688 p = 1) : d114215 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d112688 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d7327 q = 1) (hb : d112688 q = 1) : d114188 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d7327, d114188, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18299 q ha hb
    | true =>
      simp only [d7327, d114188, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d7328 q = 1) (hb : d112688 q = 1) : d114189 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d7328, d114189, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7328, d114189, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d7242 q = 1) (hb : d112688 q = 1) : d114102 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d7242, d114102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18284 q ha hb
    | true =>
      simp only [d7242, d114102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d7243 q = 1) (hb : d112688 q = 1) : d114103 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d7243, d114103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7243, d114103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d7329 q = 1) (hb : d112688 q = 1) : d114190 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d7329, d114190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d7329, d114190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d7330 q = 1) (hb : d112688 q = 1) : d114191 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d7330, d114191, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d7330, d114191, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d7331 q = 1) (hb : d112688 q = 1) : d114192 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d7331, d114192, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d7331, d114192, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d7363 q = 1) (hb : d112688 q = 1) : d114215 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d7363, d114215, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d7363, d114215, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro18306 (p : Pattern) (ha : d7368 p = 1) (hb : d112688 p = 1) : d114218 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d112688 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d7242 q = 1) (hb : d112688 q = 1) : d114102 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d7242, d114102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18284 q ha hb
    | true =>
      simp only [d7242, d114102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d7243 q = 1) (hb : d112688 q = 1) : d114103 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d7243, d114103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7243, d114103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d7344 q = 1) (hb : d112688 q = 1) : d114196 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d7344, d114196, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d7344, d114196, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d7345 q = 1) (hb : d112688 q = 1) : d114197 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d7345, d114197, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d7345, d114197, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d7346 q = 1) (hb : d112688 q = 1) : d114198 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d7346, d114198, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d7346, d114198, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d7368 q = 1) (hb : d112688 q = 1) : d114218 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d7368, d114218, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d7368, d114218, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro18307 (p : Pattern) (ha : d85437 p = 1) (hb : d112688 p = 1) : d114224 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d112688 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d116 q = 1) (hb : d112688 q = 1) : d116 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d7315 q = 1) (hb : d112688 q = 1) : d114175 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7315, d114175, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18297 q ha hb
    | true =>
      simp only [d7315, d114175, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d7316 q = 1) (hb : d112688 q = 1) : d114176 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d7316, d114176, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7316, d114176, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d7317 q = 1) (hb : d112688 q = 1) : d114177 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d7317, d114177, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d7317, d114177, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d7318 q = 1) (hb : d112688 q = 1) : d114178 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d7318, d114178, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7318, d114178, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d123 q = 1) (hb : d112688 q = 1) : d123 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d7322 q = 1) (hb : d112688 q = 1) : d114182 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7322, d114182, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18298 q ha hb
    | true =>
      simp only [d7322, d114182, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d7323 q = 1) (hb : d112688 q = 1) : d114183 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d7323, d114183, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7323, d114183, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d7324 q = 1) (hb : d112688 q = 1) : d114184 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d7324, d114184, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d7324, d114184, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d7333 q = 1) (hb : d112688 q = 1) : d114194 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7333, d114194, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18300 q ha hb
    | true =>
      simp only [d7333, d114194, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18285 q ha hb
  have h11 (q : Pattern) (ha : d85428 q = 1) (hb : d112688 q = 1) : d114195 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d85428, d114195, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d85428, d114195, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d7348 q = 1) (hb : d112688 q = 1) : d114200 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7348, d114200, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18301 q ha hb
    | true =>
      simp only [d7348, d114200, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d7349 q = 1) (hb : d112688 q = 1) : d114201 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d7349, d114201, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d7349, d114201, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d85429 q = 1) (hb : d112688 q = 1) : d114202 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d85429, d114202, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d85429, d114202, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d85430 q = 1) (hb : d112688 q = 1) : d114203 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d85430, d114203, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d85430, d114203, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d85431 q = 1) (hb : d112688 q = 1) : d114204 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d85431, d114204, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d85431, d114204, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d194 q = 1) (hb : d112688 q = 1) : d194 q = 1 := by
    exact ha
  have h18 (q : Pattern) (ha : d7355 q = 1) (hb : d112688 q = 1) : d114207 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7355, d114207, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18303 q ha hb
    | true =>
      simp only [d7355, d114207, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d7356 q = 1) (hb : d112688 q = 1) : d114208 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d7356, d114208, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7356, d114208, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d7357 q = 1) (hb : d112688 q = 1) : d114209 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d7357, d114209, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d7357, d114209, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h21 (q : Pattern) (ha : d7358 q = 1) (hb : d112688 q = 1) : d114210 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d7358, d114210, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7358, d114210, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
  have h22 (q : Pattern) (ha : d199 q = 1) (hb : d112688 q = 1) : d199 q = 1 := by
    exact ha
  have h23 (q : Pattern) (ha : d7360 q = 1) (hb : d112688 q = 1) : d114212 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7360, d114212, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18304 q ha hb
    | true =>
      simp only [d7360, d114212, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
  have h24 (q : Pattern) (ha : d7361 q = 1) (hb : d112688 q = 1) : d114213 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d7361, d114213, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7361, d114213, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
  have h25 (q : Pattern) (ha : d7362 q = 1) (hb : d112688 q = 1) : d114214 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d7362, d114214, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q ha hb
    | true =>
      simp only [d7362, d114214, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h26 (q : Pattern) (ha : d7364 q = 1) (hb : d112688 q = 1) : d114216 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7364, d114216, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18305 q ha hb
    | true =>
      simp only [d7364, d114216, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18287 q ha hb
  have h27 (q : Pattern) (ha : d85433 q = 1) (hb : d112688 q = 1) : d114217 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d85433, d114217, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h26 q ha hb
    | true =>
      simp only [d85433, d114217, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h28 (q : Pattern) (ha : d7369 q = 1) (hb : d112688 q = 1) : d114219 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7369, d114219, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18306 q ha hb
    | true =>
      simp only [d7369, d114219, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h29 (q : Pattern) (ha : d7370 q = 1) (hb : d112688 q = 1) : d114220 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d7370, d114220, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h28 q ha hb
    | true =>
      simp only [d7370, d114220, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h30 (q : Pattern) (ha : d85434 q = 1) (hb : d112688 q = 1) : d114221 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d85434, d114221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h27 q ha hb
    | true =>
      simp only [d85434, d114221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h29 q ha hb
  have h31 (q : Pattern) (ha : d85435 q = 1) (hb : d112688 q = 1) : d114222 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d85435, d114222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q ha hb
    | true =>
      simp only [d85435, d114222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h30 q ha hb
  have h32 (q : Pattern) (ha : d85436 q = 1) (hb : d112688 q = 1) : d114223 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d85436, d114223, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d85436, d114223, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h31 q ha hb
  have h33 (q : Pattern) (ha : d85437 q = 1) (hb : d112688 q = 1) : d114224 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d85437, d114224, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d85437, d114224, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h32 q ha hb
  exact h33 p ha hb
theorem andIntro18308 (p : Pattern) (ha : d85444 p = 1) (hb : d112688 p = 1) : d114233 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d112688 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d7364 q = 1) (hb : d112688 q = 1) : d114216 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7364, d114216, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18305 q ha hb
    | true =>
      simp only [d7364, d114216, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18287 q ha hb
  have h2 (q : Pattern) (ha : d85433 q = 1) (hb : d112688 q = 1) : d114217 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d85433, d114217, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d85433, d114217, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d7369 q = 1) (hb : d112688 q = 1) : d114219 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7369, d114219, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18306 q ha hb
    | true =>
      simp only [d7369, d114219, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d7370 q = 1) (hb : d112688 q = 1) : d114220 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d7370, d114220, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d7370, d114220, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d85434 q = 1) (hb : d112688 q = 1) : d114221 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d85434, d114221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d85434, d114221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d85442 q = 1) (hb : d112688 q = 1) : d114231 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d85442, d114231, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d85442, d114231, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d85443 q = 1) (hb : d112688 q = 1) : d114232 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d85443, d114232, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d85443, d114232, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d85444 q = 1) (hb : d112688 q = 1) : d114233 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d85444, d114233, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d85444, d114233, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro18309 (p : Pattern) (ha : d7390 p = 1) (hb : d112688 p = 1) : d114241 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d94753 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d418 q = 1) (hb : d94753 q = 1) : d12387 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d418, d12387, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12479 q ha hb
    | true =>
      simp only [d418, d12387, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12435 q ha hb
  have h2 (q : Pattern) (ha : d419 q = 1) (hb : d94753 q = 1) : d12388 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d419, d12388, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d419, d12388, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d420 q = 1) (hb : d94753 q = 1) : d12389 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d420, d12389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d420, d12389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d112686 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d71 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d232 q = 1) (hb : d112686 q = 1) : d88402 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d232, d112686, d88402, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12435 q ha hb
    | true =>
      simp only [d232, d112686, d88402, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d233 q = 1) (hb : d112686 q = 1) : d88403 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d233, d88403, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d233, d88403, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d234 q = 1) (hb : d112686 q = 1) : d88404 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d234, d88404, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d234, d88404, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d421 q = 1) (hb : d112687 q = 1) : d114239 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d421, d112687, d114239, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d421, d112687, d114239, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d7389 q = 1) (hb : d112688 q = 1) : d114240 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d7389, d112688, d114240, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d7389, d112688, d114240, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d112688 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d7390 q = 1) (hb : d112688 q = 1) : d114241 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d7390, d114241, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d7390, d114241, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  exact h13 p ha hb
theorem andIntro18310 (p : Pattern) (ha : d7396 p = 1) (hb : d112688 p = 1) : d114247 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d112688 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d7391 q = 1) (hb : d112688 q = 1) : d114242 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d7391, d114242, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18309 q ha hb
    | true =>
      simp only [d7391, d114242, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d7392 q = 1) (hb : d112688 q = 1) : d114243 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d7392, d114243, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7392, d114243, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d7275 q = 1) (hb : d112688 q = 1) : d114135 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d7275, d114135, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18290 q ha hb
    | true =>
      simp only [d7275, d114135, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d7276 q = 1) (hb : d112688 q = 1) : d114136 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d7276, d114136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7276, d114136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d7393 q = 1) (hb : d112688 q = 1) : d114244 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d7393, d114244, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d7393, d114244, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d7394 q = 1) (hb : d112688 q = 1) : d114245 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d7394, d114245, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d7394, d114245, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d7395 q = 1) (hb : d112688 q = 1) : d114246 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d7395, d114246, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d7395, d114246, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d7396 q = 1) (hb : d112688 q = 1) : d114247 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d7396, d114247, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d7396, d114247, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro18311 (p : Pattern) (ha : d7411 p = 1) (hb : d112688 p = 1) : d114253 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d112688 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d7275 q = 1) (hb : d112688 q = 1) : d114135 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d7275, d114135, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18290 q ha hb
    | true =>
      simp only [d7275, d114135, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d7276 q = 1) (hb : d112688 q = 1) : d114136 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d7276, d114136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7276, d114136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d7408 q = 1) (hb : d112688 q = 1) : d114250 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d7408, d114250, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d7408, d114250, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d7409 q = 1) (hb : d112688 q = 1) : d114251 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d7409, d114251, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d7409, d114251, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d7410 q = 1) (hb : d112688 q = 1) : d114252 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d7410, d114252, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d7410, d114252, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d7411 q = 1) (hb : d112688 q = 1) : d114253 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d7411, d114253, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d7411, d114253, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro18312 (p : Pattern) (ha : d85454 p = 1) (hb : d112688 p = 1) : d114259 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d112688 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d7397 q = 1) (hb : d112688 q = 1) : d114248 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7397, d114248, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18310 q ha hb
    | true =>
      simp only [d7397, d114248, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18291 q ha hb
  have h2 (q : Pattern) (ha : d85450 q = 1) (hb : d112688 q = 1) : d114249 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d85450, d114249, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d85450, d114249, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d7412 q = 1) (hb : d112688 q = 1) : d114254 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7412, d114254, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18311 q ha hb
    | true =>
      simp only [d7412, d114254, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d7413 q = 1) (hb : d112688 q = 1) : d114255 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d7413, d114255, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d7413, d114255, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d85451 q = 1) (hb : d112688 q = 1) : d114256 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d85451, d114256, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d85451, d114256, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d85452 q = 1) (hb : d112688 q = 1) : d114257 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d85452, d114257, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d85452, d114257, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d85453 q = 1) (hb : d112688 q = 1) : d114258 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d85453, d114258, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d85453, d114258, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d85454 q = 1) (hb : d112688 q = 1) : d114259 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d85454, d114259, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d85454, d114259, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro18313 (p : Pattern) (ha : d85460 p = 1) (hb : d112688 p = 1) : d114265 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d112688 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d7303 q = 1) (hb : d112688 q = 1) : d114163 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d7303, d114163, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7303, d114163, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18294 q ha hb
  have h2 (q : Pattern) (ha : d7304 q = 1) (hb : d112688 q = 1) : d114164 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d7304, d114164, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d7304, d114164, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d7310 q = 1) (hb : d112688 q = 1) : d114170 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d7310, d114170, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18294 q ha hb
    | true =>
      simp only [d7310, d114170, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18295 q ha hb
  have h4 (q : Pattern) (ha : d7311 q = 1) (hb : d112688 q = 1) : d114171 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d7311, d114171, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d7311, d114171, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d7312 q = 1) (hb : d112688 q = 1) : d114172 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d7312, d114172, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d7312, d114172, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d85438 q = 1) (hb : d112688 q = 1) : d114225 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d85438, d114225, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18302 q ha hb
    | true =>
      simp only [d85438, d114225, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18307 q ha hb
  have h7 (q : Pattern) (ha : d111 q = 1) (hb : d112688 q = 1) : d111 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d7377 q = 1) (hb : d112688 q = 1) : d114227 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d7377, d114227, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18296 q ha hb
    | true =>
      simp only [d7377, d114227, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d85439 q = 1) (hb : d112688 q = 1) : d114228 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d85439, d114228, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d85439, d114228, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d85440 q = 1) (hb : d112688 q = 1) : d114229 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d85440, d114229, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d85440, d114229, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d85441 q = 1) (hb : d112688 q = 1) : d114230 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d85441, d114230, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d85441, d114230, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d85445 q = 1) (hb : d112688 q = 1) : d114234 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d85445, d114234, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d85445, d114234, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18308 q ha hb
  have h13 (q : Pattern) (ha : d407 q = 1) (hb : d112688 q = 1) : d407 q = 1 := by
    exact ha
  have h14 (q : Pattern) (ha : d85446 q = 1) (hb : d112688 q = 1) : d114235 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d85446, d114235, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d85446, d114235, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d85447 q = 1) (hb : d112688 q = 1) : d114236 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d85447, d114236, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d85447, d114236, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h16 (q : Pattern) (ha : d85448 q = 1) (hb : d112688 q = 1) : d114237 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d85448, d114237, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d85448, d114237, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h17 (q : Pattern) (ha : d85449 q = 1) (hb : d112688 q = 1) : d114238 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d85449, d114238, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d85449, d114238, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d85455 q = 1) (hb : d112688 q = 1) : d114260 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d85455, d114260, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d85455, d114260, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18312 q ha hb
  have h19 (q : Pattern) (ha : d463 q = 1) (hb : d112688 q = 1) : d463 q = 1 := by
    exact ha
  have h20 (q : Pattern) (ha : d85456 q = 1) (hb : d112688 q = 1) : d114261 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d85456, d114261, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d85456, d114261, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
  have h21 (q : Pattern) (ha : d85457 q = 1) (hb : d112688 q = 1) : d114262 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d85457, d114262, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d85457, d114262, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h22 (q : Pattern) (ha : d85458 q = 1) (hb : d112688 q = 1) : d114263 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d85458, d114263, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d85458, d114263, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h23 (q : Pattern) (ha : d85459 q = 1) (hb : d112688 q = 1) : d114264 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d85459, d114264, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
    | true =>
      simp only [d85459, d114264, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h24 (q : Pattern) (ha : d85460 q = 1) (hb : d112688 q = 1) : d114265 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d85460, d114265, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d85460, d114265, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
  exact h24 p ha hb
theorem andIntro18314 (p : Pattern) (ha : d85466 p = 1) (hb : d112688 p = 1) : d114271 p = 1 := by
  have h0 (q : Pattern) (ha : d99 q = 1) (hb : d112688 q = 1) : d99 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d112688 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d85423 q = 1) (hb : d112688 q = 1) : d114153 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d85423, d114153, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d85423, d114153, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18293 q ha hb
  have h3 (q : Pattern) (ha : d85424 q = 1) (hb : d112688 q = 1) : d114154 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d85424, d114154, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d85424, d114154, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d85425 q = 1) (hb : d112688 q = 1) : d114155 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d85425, d114155, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d85425, d114155, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d85426 q = 1) (hb : d112688 q = 1) : d114156 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d85426, d114156, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d85426, d114156, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d85427 q = 1) (hb : d112688 q = 1) : d114157 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d85427, d114157, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d85427, d114157, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d85461 q = 1) (hb : d112688 q = 1) : d114266 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d85461, d114266, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d85461, d114266, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18313 q ha hb
  have h8 (q : Pattern) (ha : d85462 q = 1) (hb : d112688 q = 1) : d114267 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d85462, d114267, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d85462, d114267, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d85463 q = 1) (hb : d112688 q = 1) : d114268 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d85463, d114268, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d85463, d114268, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d85464 q = 1) (hb : d112688 q = 1) : d114269 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d85464, d114269, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d85464, d114269, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d85465 q = 1) (hb : d112688 q = 1) : d114270 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d85465, d114270, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d85465, d114270, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d85466 q = 1) (hb : d112688 q = 1) : d114271 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d85466, d114271, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d85466, d114271, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  exact h12 p ha hb
theorem andIntro18315 (p : Pattern) (ha : d481 p = 1) (hb : d112688 p = 1) : d12442 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d94753 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d30 q = 1) (hb : d94753 q = 1) : d30 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d145 q = 1) (hb : d94753 q = 1) : d4819 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d145, d4819, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12423 q ha hb
    | true =>
      simp only [d145, d4819, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d146 q = 1) (hb : d94753 q = 1) : d4820 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d146, d4820, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d146, d4820, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d147 q = 1) (hb : d94753 q = 1) : d4821 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d147, d4821, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d147, d4821, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d112686 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d475 q = 1) (hb : d112687 q = 1) : d4822 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d475, d112687, d4822, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d475, d112687, d4822, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d480 q = 1) (hb : d112688 q = 1) : d12441 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d480, d112688, d12441, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d480, d112688, d12441, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d112688 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d481 q = 1) (hb : d112688 q = 1) : d12442 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d481, d12442, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d481, d12442, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro18316 (p : Pattern) (ha : d491 p = 1) (hb : d112688 p = 1) : d12452 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d112688 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d482 q = 1) (hb : d112688 q = 1) : d12443 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d482, d12443, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18315 q ha hb
    | true =>
      simp only [d482, d12443, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d483 q = 1) (hb : d112688 q = 1) : d12444 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d483, d12444, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d483, d12444, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d488 q = 1) (hb : d112688 q = 1) : d12449 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d488, d12449, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d488, d12449, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d489 q = 1) (hb : d112688 q = 1) : d12450 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d489, d12450, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d489, d12450, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d490 q = 1) (hb : d112688 q = 1) : d12451 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d490, d12451, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d490, d12451, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d491 q = 1) (hb : d112688 q = 1) : d12452 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d491, d12452, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d491, d12452, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro18317 (p : Pattern) (ha : d501 p = 1) (hb : d112688 p = 1) : d12462 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d112688 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d482 q = 1) (hb : d112688 q = 1) : d12443 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d482, d12443, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18315 q ha hb
    | true =>
      simp only [d482, d12443, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d483 q = 1) (hb : d112688 q = 1) : d12444 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d483, d12444, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d483, d12444, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d488 q = 1) (hb : d112688 q = 1) : d12449 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d488, d12449, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d488, d12449, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d489 q = 1) (hb : d112688 q = 1) : d12450 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d489, d12450, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d489, d12450, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d490 q = 1) (hb : d112688 q = 1) : d12451 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d490, d12451, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d490, d12451, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d501 q = 1) (hb : d112688 q = 1) : d12462 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d501, d12462, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d501, d12462, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro18318 (p : Pattern) (ha : d644 p = 1) (hb : d112688 p = 1) : d12580 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d112688 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d633 q = 1) (hb : d112688 q = 1) : d12569 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d633, d12569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18316 q ha hb
    | true =>
      simp only [d633, d12569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d634 q = 1) (hb : d112688 q = 1) : d12570 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d634, d12570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d634, d12570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d635 q = 1) (hb : d112688 q = 1) : d12571 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d635, d12571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d635, d12571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d636 q = 1) (hb : d112688 q = 1) : d12572 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d636, d12572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d636, d12572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d637 q = 1) (hb : d112688 q = 1) : d12573 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d637, d12573, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d637, d12573, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d639 q = 1) (hb : d112688 q = 1) : d12575 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d639, d12575, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18317 q ha hb
    | true =>
      simp only [d639, d12575, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d640 q = 1) (hb : d112688 q = 1) : d12576 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d640, d12576, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d640, d12576, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d641 q = 1) (hb : d112688 q = 1) : d12577 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d641, d12577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d641, d12577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d642 q = 1) (hb : d112688 q = 1) : d12578 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d642, d12578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d642, d12578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d643 q = 1) (hb : d112688 q = 1) : d12579 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d643, d12579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d643, d12579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d644 q = 1) (hb : d112688 q = 1) : d12580 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d644, d12580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d644, d12580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro18319 (p : Pattern) (ha : d653 p = 1) (hb : d112688 p = 1) : d12589 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d112688 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d639 q = 1) (hb : d112688 q = 1) : d12575 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d639, d12575, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18317 q ha hb
    | true =>
      simp only [d639, d12575, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d640 q = 1) (hb : d112688 q = 1) : d12576 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d640, d12576, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d640, d12576, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d641 q = 1) (hb : d112688 q = 1) : d12577 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d641, d12577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d641, d12577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d642 q = 1) (hb : d112688 q = 1) : d12578 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d642, d12578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d642, d12578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d643 q = 1) (hb : d112688 q = 1) : d12579 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d643, d12579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d643, d12579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d653 q = 1) (hb : d112688 q = 1) : d12589 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d653, d12589, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d653, d12589, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro18320 (p : Pattern) (ha : d683 p = 1) (hb : d112688 p = 1) : d12622 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d94753 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d71 q = 1) (hb : d94753 q = 1) : d71 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d232 q = 1) (hb : d94753 q = 1) : d6079 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d232, d6079, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12435 q ha hb
    | true =>
      simp only [d232, d6079, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d233 q = 1) (hb : d94753 q = 1) : d6080 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d233, d6080, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d233, d6080, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d234 q = 1) (hb : d94753 q = 1) : d6081 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d234, d6081, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d234, d6081, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d112686 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d673 q = 1) (hb : d112687 q = 1) : d6082 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d673, d112687, d6082, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d673, d112687, d6082, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d682 q = 1) (hb : d112688 q = 1) : d12621 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d682, d112688, d12621, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d682, d112688, d12621, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d112688 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d683 q = 1) (hb : d112688 q = 1) : d12622 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d683, d12622, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d683, d12622, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro18321 (p : Pattern) (ha : d730 p = 1) (hb : d112688 p = 1) : d12668 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d112688 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d684 q = 1) (hb : d112688 q = 1) : d12623 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d684, d12623, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18320 q ha hb
    | true =>
      simp only [d684, d12623, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d685 q = 1) (hb : d112688 q = 1) : d12624 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d685, d12624, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d685, d12624, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d727 q = 1) (hb : d112688 q = 1) : d12665 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d727, d12665, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d727, d12665, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d728 q = 1) (hb : d112688 q = 1) : d12666 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d728, d12666, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d728, d12666, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d729 q = 1) (hb : d112688 q = 1) : d12667 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d729, d12667, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d729, d12667, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d730 q = 1) (hb : d112688 q = 1) : d12668 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d730, d12668, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d730, d12668, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro18322 (p : Pattern) (ha : d736 p = 1) (hb : d112688 p = 1) : d12674 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d112688 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d731 q = 1) (hb : d112688 q = 1) : d12669 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d731, d12669, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18321 q ha hb
    | true =>
      simp only [d731, d12669, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d732 q = 1) (hb : d112688 q = 1) : d12670 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d732, d12670, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d732, d12670, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d733 q = 1) (hb : d112688 q = 1) : d12671 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d733, d12671, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d733, d12671, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d734 q = 1) (hb : d112688 q = 1) : d12672 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d734, d12672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d734, d12672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d735 q = 1) (hb : d112688 q = 1) : d12673 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d735, d12673, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d735, d12673, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d736 q = 1) (hb : d112688 q = 1) : d12674 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d736, d12674, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d736, d12674, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro18323 (p : Pattern) (ha : d7433 p = 1) (hb : d112688 p = 1) : d114275 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d112688 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d7327 q = 1) (hb : d112688 q = 1) : d114188 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d7327, d114188, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18299 q ha hb
    | true =>
      simp only [d7327, d114188, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d7328 q = 1) (hb : d112688 q = 1) : d114189 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d7328, d114189, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7328, d114189, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d482 q = 1) (hb : d112688 q = 1) : d12443 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d482, d12443, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18315 q ha hb
    | true =>
      simp only [d482, d12443, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d483 q = 1) (hb : d112688 q = 1) : d12444 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d483, d12444, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d483, d12444, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d7430 q = 1) (hb : d112688 q = 1) : d114272 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d7430, d114272, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d7430, d114272, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d7431 q = 1) (hb : d112688 q = 1) : d114273 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d7431, d114273, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d7431, d114273, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d7432 q = 1) (hb : d112688 q = 1) : d114274 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d7432, d114274, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d7432, d114274, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d7433 q = 1) (hb : d112688 q = 1) : d114275 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d7433, d114275, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7433, d114275, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro18324 (p : Pattern) (ha : d7439 p = 1) (hb : d112688 p = 1) : d114281 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d112688 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d7434 q = 1) (hb : d112688 q = 1) : d114276 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7434, d114276, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18323 q ha hb
    | true =>
      simp only [d7434, d114276, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18316 q ha hb
  have h2 (q : Pattern) (ha : d7435 q = 1) (hb : d112688 q = 1) : d114277 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d7435, d114277, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7435, d114277, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d7436 q = 1) (hb : d112688 q = 1) : d114278 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d7436, d114278, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d7436, d114278, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d7437 q = 1) (hb : d112688 q = 1) : d114279 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d7437, d114279, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7437, d114279, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d7438 q = 1) (hb : d112688 q = 1) : d114280 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d7438, d114280, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7438, d114280, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d7439 q = 1) (hb : d112688 q = 1) : d114281 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d7439, d114281, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7439, d114281, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro18325 (p : Pattern) (ha : d7442 p = 1) (hb : d112688 p = 1) : d114284 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d112688 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d7327 q = 1) (hb : d112688 q = 1) : d114188 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d7327, d114188, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18299 q ha hb
    | true =>
      simp only [d7327, d114188, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d7328 q = 1) (hb : d112688 q = 1) : d114189 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d7328, d114189, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7328, d114189, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d482 q = 1) (hb : d112688 q = 1) : d12443 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d482, d12443, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18315 q ha hb
    | true =>
      simp only [d482, d12443, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d483 q = 1) (hb : d112688 q = 1) : d12444 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d483, d12444, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d483, d12444, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d7430 q = 1) (hb : d112688 q = 1) : d114272 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d7430, d114272, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d7430, d114272, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d7431 q = 1) (hb : d112688 q = 1) : d114273 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d7431, d114273, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d7431, d114273, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d7432 q = 1) (hb : d112688 q = 1) : d114274 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d7432, d114274, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d7432, d114274, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d7442 q = 1) (hb : d112688 q = 1) : d114284 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d7442, d114284, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d7442, d114284, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro18326 (p : Pattern) (ha : d7448 p = 1) (hb : d112688 p = 1) : d114290 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d112688 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d7434 q = 1) (hb : d112688 q = 1) : d114276 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7434, d114276, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18323 q ha hb
    | true =>
      simp only [d7434, d114276, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18316 q ha hb
  have h2 (q : Pattern) (ha : d7435 q = 1) (hb : d112688 q = 1) : d114277 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d7435, d114277, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7435, d114277, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d7436 q = 1) (hb : d112688 q = 1) : d114278 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d7436, d114278, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d7436, d114278, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d7437 q = 1) (hb : d112688 q = 1) : d114279 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d7437, d114279, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7437, d114279, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d7438 q = 1) (hb : d112688 q = 1) : d114280 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d7438, d114280, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7438, d114280, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d7443 q = 1) (hb : d112688 q = 1) : d114285 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7443, d114285, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18325 q ha hb
    | true =>
      simp only [d7443, d114285, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18317 q ha hb
  have h7 (q : Pattern) (ha : d7444 q = 1) (hb : d112688 q = 1) : d114286 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d7444, d114286, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7444, d114286, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d7445 q = 1) (hb : d112688 q = 1) : d114287 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d7445, d114287, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d7445, d114287, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d7446 q = 1) (hb : d112688 q = 1) : d114288 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d7446, d114288, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7446, d114288, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d7447 q = 1) (hb : d112688 q = 1) : d114289 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d7447, d114289, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7447, d114289, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d7448 q = 1) (hb : d112688 q = 1) : d114290 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d7448, d114290, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d7448, d114290, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro18327 (p : Pattern) (ha : d7515 p = 1) (hb : d112688 p = 1) : d114350 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d112688 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d7434 q = 1) (hb : d112688 q = 1) : d114276 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7434, d114276, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18323 q ha hb
    | true =>
      simp only [d7434, d114276, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18316 q ha hb
  have h2 (q : Pattern) (ha : d7435 q = 1) (hb : d112688 q = 1) : d114277 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d7435, d114277, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7435, d114277, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d7436 q = 1) (hb : d112688 q = 1) : d114278 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d7436, d114278, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d7436, d114278, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d7437 q = 1) (hb : d112688 q = 1) : d114279 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d7437, d114279, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7437, d114279, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d7438 q = 1) (hb : d112688 q = 1) : d114280 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d7438, d114280, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7438, d114280, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d633 q = 1) (hb : d112688 q = 1) : d12569 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d633, d12569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18316 q ha hb
    | true =>
      simp only [d633, d12569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d634 q = 1) (hb : d112688 q = 1) : d12570 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d634, d12570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d634, d12570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d635 q = 1) (hb : d112688 q = 1) : d12571 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d635, d12571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d635, d12571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d636 q = 1) (hb : d112688 q = 1) : d12572 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d636, d12572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d636, d12572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d637 q = 1) (hb : d112688 q = 1) : d12573 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d637, d12573, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d637, d12573, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d7515 q = 1) (hb : d112688 q = 1) : d114350 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d7515, d114350, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d7515, d114350, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro18328 (p : Pattern) (ha : d514 p = 1) (hb : d112688 p = 1) : d12475 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d112688 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d482 q = 1) (hb : d112688 q = 1) : d12443 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d482, d12443, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18315 q ha hb
    | true =>
      simp only [d482, d12443, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d483 q = 1) (hb : d112688 q = 1) : d12444 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d483, d12444, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d483, d12444, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d488 q = 1) (hb : d112688 q = 1) : d12449 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d488, d12449, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d488, d12449, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d489 q = 1) (hb : d112688 q = 1) : d12450 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d489, d12450, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d489, d12450, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d513 q = 1) (hb : d112688 q = 1) : d12474 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d513, d12474, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d513, d12474, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d514 q = 1) (hb : d112688 q = 1) : d12475 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d514, d12475, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d514, d12475, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro18329 (p : Pattern) (ha : d524 p = 1) (hb : d112688 p = 1) : d12485 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d112688 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d482 q = 1) (hb : d112688 q = 1) : d12443 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d482, d12443, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18315 q ha hb
    | true =>
      simp only [d482, d12443, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d483 q = 1) (hb : d112688 q = 1) : d12444 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d483, d12444, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d483, d12444, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d488 q = 1) (hb : d112688 q = 1) : d12449 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d488, d12449, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d488, d12449, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d522 q = 1) (hb : d112688 q = 1) : d12483 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d522, d12483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d522, d12483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d523 q = 1) (hb : d112688 q = 1) : d12484 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d523, d12484, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d523, d12484, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d524 q = 1) (hb : d112688 q = 1) : d12485 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d524, d12485, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d524, d12485, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro18330 (p : Pattern) (ha : d7453 p = 1) (hb : d112688 p = 1) : d114295 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d112688 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d7327 q = 1) (hb : d112688 q = 1) : d114188 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d7327, d114188, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18299 q ha hb
    | true =>
      simp only [d7327, d114188, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d7328 q = 1) (hb : d112688 q = 1) : d114189 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d7328, d114189, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7328, d114189, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d482 q = 1) (hb : d112688 q = 1) : d12443 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d482, d12443, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18315 q ha hb
    | true =>
      simp only [d482, d12443, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d483 q = 1) (hb : d112688 q = 1) : d12444 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d483, d12444, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d483, d12444, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d7430 q = 1) (hb : d112688 q = 1) : d114272 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d7430, d114272, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d7430, d114272, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d7431 q = 1) (hb : d112688 q = 1) : d114273 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d7431, d114273, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d7431, d114273, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d7452 q = 1) (hb : d112688 q = 1) : d114294 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d7452, d114294, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7452, d114294, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d7453 q = 1) (hb : d112688 q = 1) : d114295 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d7453, d114295, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7453, d114295, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro18331 (p : Pattern) (ha : d7460 p = 1) (hb : d112688 p = 1) : d114302 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d112688 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d7327 q = 1) (hb : d112688 q = 1) : d114188 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d7327, d114188, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18299 q ha hb
    | true =>
      simp only [d7327, d114188, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d7328 q = 1) (hb : d112688 q = 1) : d114189 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d7328, d114189, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7328, d114189, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d482 q = 1) (hb : d112688 q = 1) : d12443 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d482, d12443, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18315 q ha hb
    | true =>
      simp only [d482, d12443, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d483 q = 1) (hb : d112688 q = 1) : d12444 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d483, d12444, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d483, d12444, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d7430 q = 1) (hb : d112688 q = 1) : d114272 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d7430, d114272, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d7430, d114272, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d7458 q = 1) (hb : d112688 q = 1) : d114300 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d7458, d114300, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7458, d114300, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d7459 q = 1) (hb : d112688 q = 1) : d114301 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d7459, d114301, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d7459, d114301, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d7460 q = 1) (hb : d112688 q = 1) : d114302 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d7460, d114302, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7460, d114302, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro18332 (p : Pattern) (ha : d548 p = 1) (hb : d94753 p = 1) : d12489 p = 1 := by
  have h0 (q : Pattern) (ha : d1 q = 1) (hb : d547 q = 1) : d547 q = 1 := by
    exact hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d323 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d548 q = 1) (hb : d94753 q = 1) : d12489 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d548, d94753, d12489, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d548, d94753, d12489, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  exact h2 p ha hb
theorem andIntro18333 (p : Pattern) (ha : d7465 p = 1) (hb : d112688 p = 1) : d114311 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d94753 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d549 q = 1) (hb : d94753 q = 1) : d12490 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d549, d12490, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18332 q ha hb
    | true =>
      simp only [d549, d12490, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12463 q ha hb
  have h2 (q : Pattern) (ha : d550 q = 1) (hb : d94753 q = 1) : d12491 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d550, d12491, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d550, d12491, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d551 q = 1) (hb : d94753 q = 1) : d12492 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d551, d12492, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d551, d12492, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d112686 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d144 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d325 q = 1) (hb : d112686 q = 1) : d114306 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d325, d112686, d114306, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12463 q ha hb
    | true =>
      simp only [d325, d112686, d114306, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d326 q = 1) (hb : d112686 q = 1) : d114307 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d326, d114307, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d326, d114307, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d327 q = 1) (hb : d112686 q = 1) : d114308 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d327, d114308, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d327, d114308, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d552 q = 1) (hb : d112687 q = 1) : d114309 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d552, d112687, d114309, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d552, d112687, d114309, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d7464 q = 1) (hb : d112688 q = 1) : d114310 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d7464, d112688, d114310, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d7464, d112688, d114310, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d112688 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d7465 q = 1) (hb : d112688 q = 1) : d114311 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d7465, d114311, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d7465, d114311, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  exact h13 p ha hb
theorem andIntro18334 (p : Pattern) (ha : d7471 p = 1) (hb : d112688 p = 1) : d114317 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d112688 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d7466 q = 1) (hb : d112688 q = 1) : d114312 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d7466, d114312, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18333 q ha hb
    | true =>
      simp only [d7466, d114312, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d7467 q = 1) (hb : d112688 q = 1) : d114313 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d7467, d114313, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7467, d114313, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d7327 q = 1) (hb : d112688 q = 1) : d114188 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d7327, d114188, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18299 q ha hb
    | true =>
      simp only [d7327, d114188, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d7328 q = 1) (hb : d112688 q = 1) : d114189 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d7328, d114189, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7328, d114189, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d7468 q = 1) (hb : d112688 q = 1) : d114314 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d7468, d114314, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d7468, d114314, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d7469 q = 1) (hb : d112688 q = 1) : d114315 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d7469, d114315, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d7469, d114315, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d7470 q = 1) (hb : d112688 q = 1) : d114316 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d7470, d114316, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d7470, d114316, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d7471 q = 1) (hb : d112688 q = 1) : d114317 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d7471, d114317, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7471, d114317, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro18335 (p : Pattern) (ha : d7486 p = 1) (hb : d112688 p = 1) : d114323 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d112688 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d7327 q = 1) (hb : d112688 q = 1) : d114188 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d7327, d114188, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18299 q ha hb
    | true =>
      simp only [d7327, d114188, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d7328 q = 1) (hb : d112688 q = 1) : d114189 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d7328, d114189, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7328, d114189, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d7483 q = 1) (hb : d112688 q = 1) : d114320 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d7483, d114320, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d7483, d114320, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d7484 q = 1) (hb : d112688 q = 1) : d114321 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d7484, d114321, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d7484, d114321, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d7485 q = 1) (hb : d112688 q = 1) : d114322 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d7485, d114322, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d7485, d114322, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d7486 q = 1) (hb : d112688 q = 1) : d114323 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d7486, d114323, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7486, d114323, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro18336 (p : Pattern) (ha : d85471 p = 1) (hb : d112688 p = 1) : d114329 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d112688 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d7454 q = 1) (hb : d112688 q = 1) : d114296 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7454, d114296, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18330 q ha hb
    | true =>
      simp only [d7454, d114296, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18328 q ha hb
  have h2 (q : Pattern) (ha : d7455 q = 1) (hb : d112688 q = 1) : d114297 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d7455, d114297, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7455, d114297, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d7456 q = 1) (hb : d112688 q = 1) : d114298 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d7456, d114298, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d7456, d114298, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d7457 q = 1) (hb : d112688 q = 1) : d114299 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d7457, d114299, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7457, d114299, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d7461 q = 1) (hb : d112688 q = 1) : d114303 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7461, d114303, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18331 q ha hb
    | true =>
      simp only [d7461, d114303, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18329 q ha hb
  have h6 (q : Pattern) (ha : d7462 q = 1) (hb : d112688 q = 1) : d114304 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d7462, d114304, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7462, d114304, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d7463 q = 1) (hb : d112688 q = 1) : d114305 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d7463, d114305, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d7463, d114305, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d7472 q = 1) (hb : d112688 q = 1) : d114318 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7472, d114318, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18334 q ha hb
    | true =>
      simp only [d7472, d114318, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18323 q ha hb
  have h9 (q : Pattern) (ha : d85467 q = 1) (hb : d112688 q = 1) : d114319 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d85467, d114319, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d85467, d114319, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d7487 q = 1) (hb : d112688 q = 1) : d114324 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7487, d114324, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18335 q ha hb
    | true =>
      simp only [d7487, d114324, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d7488 q = 1) (hb : d112688 q = 1) : d114325 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d7488, d114325, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d7488, d114325, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d85468 q = 1) (hb : d112688 q = 1) : d114326 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d85468, d114326, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d85468, d114326, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d85469 q = 1) (hb : d112688 q = 1) : d114327 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d85469, d114327, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d85469, d114327, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d85470 q = 1) (hb : d112688 q = 1) : d114328 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d85470, d114328, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d85470, d114328, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d85471 q = 1) (hb : d112688 q = 1) : d114329 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d85471, d114329, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d85471, d114329, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro18337 (p : Pattern) (ha : d610 p = 1) (hb : d112688 p = 1) : d12545 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d112688 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d482 q = 1) (hb : d112688 q = 1) : d12443 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d482, d12443, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18315 q ha hb
    | true =>
      simp only [d482, d12443, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d483 q = 1) (hb : d112688 q = 1) : d12444 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d483, d12444, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d483, d12444, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d488 q = 1) (hb : d112688 q = 1) : d12449 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d488, d12449, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d488, d12449, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d489 q = 1) (hb : d112688 q = 1) : d12450 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d489, d12450, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d489, d12450, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d513 q = 1) (hb : d112688 q = 1) : d12474 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d513, d12474, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d513, d12474, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d610 q = 1) (hb : d112688 q = 1) : d12545 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d610, d12545, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d610, d12545, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro18338 (p : Pattern) (ha : d616 p = 1) (hb : d112688 p = 1) : d12551 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d112688 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d482 q = 1) (hb : d112688 q = 1) : d12443 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d482, d12443, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18315 q ha hb
    | true =>
      simp only [d482, d12443, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d483 q = 1) (hb : d112688 q = 1) : d12444 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d483, d12444, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d483, d12444, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d488 q = 1) (hb : d112688 q = 1) : d12449 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d488, d12449, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d488, d12449, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d522 q = 1) (hb : d112688 q = 1) : d12483 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d522, d12483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d522, d12483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d523 q = 1) (hb : d112688 q = 1) : d12484 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d523, d12484, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d523, d12484, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d616 q = 1) (hb : d112688 q = 1) : d12551 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d616, d12551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d616, d12551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro18339 (p : Pattern) (ha : d7493 p = 1) (hb : d112688 p = 1) : d114330 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d112688 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d7327 q = 1) (hb : d112688 q = 1) : d114188 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d7327, d114188, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18299 q ha hb
    | true =>
      simp only [d7327, d114188, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d7328 q = 1) (hb : d112688 q = 1) : d114189 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d7328, d114189, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7328, d114189, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d482 q = 1) (hb : d112688 q = 1) : d12443 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d482, d12443, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18315 q ha hb
    | true =>
      simp only [d482, d12443, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d483 q = 1) (hb : d112688 q = 1) : d12444 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d483, d12444, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d483, d12444, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d7430 q = 1) (hb : d112688 q = 1) : d114272 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d7430, d114272, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d7430, d114272, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d7431 q = 1) (hb : d112688 q = 1) : d114273 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d7431, d114273, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d7431, d114273, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d7452 q = 1) (hb : d112688 q = 1) : d114294 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d7452, d114294, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7452, d114294, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d7493 q = 1) (hb : d112688 q = 1) : d114330 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d7493, d114330, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d7493, d114330, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro18340 (p : Pattern) (ha : d7498 p = 1) (hb : d112688 p = 1) : d114335 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d112688 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d7327 q = 1) (hb : d112688 q = 1) : d114188 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d7327, d114188, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18299 q ha hb
    | true =>
      simp only [d7327, d114188, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d7328 q = 1) (hb : d112688 q = 1) : d114189 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d7328, d114189, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7328, d114189, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d482 q = 1) (hb : d112688 q = 1) : d12443 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d482, d12443, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18315 q ha hb
    | true =>
      simp only [d482, d12443, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d483 q = 1) (hb : d112688 q = 1) : d12444 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d483, d12444, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d483, d12444, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d7430 q = 1) (hb : d112688 q = 1) : d114272 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d7430, d114272, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d7430, d114272, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d7458 q = 1) (hb : d112688 q = 1) : d114300 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d7458, d114300, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7458, d114300, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d7459 q = 1) (hb : d112688 q = 1) : d114301 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d7459, d114301, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d7459, d114301, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d7498 q = 1) (hb : d112688 q = 1) : d114335 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d7498, d114335, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d7498, d114335, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro18341 (p : Pattern) (ha : d7502 p = 1) (hb : d112688 p = 1) : d114339 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d112688 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d7466 q = 1) (hb : d112688 q = 1) : d114312 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d7466, d114312, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18333 q ha hb
    | true =>
      simp only [d7466, d114312, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d7467 q = 1) (hb : d112688 q = 1) : d114313 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d7467, d114313, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7467, d114313, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d7327 q = 1) (hb : d112688 q = 1) : d114188 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d7327, d114188, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18299 q ha hb
    | true =>
      simp only [d7327, d114188, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d7328 q = 1) (hb : d112688 q = 1) : d114189 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d7328, d114189, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7328, d114189, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d7468 q = 1) (hb : d112688 q = 1) : d114314 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d7468, d114314, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d7468, d114314, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d7469 q = 1) (hb : d112688 q = 1) : d114315 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d7469, d114315, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d7469, d114315, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d7470 q = 1) (hb : d112688 q = 1) : d114316 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d7470, d114316, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d7470, d114316, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d7502 q = 1) (hb : d112688 q = 1) : d114339 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d7502, d114339, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d7502, d114339, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro18342 (p : Pattern) (ha : d7507 p = 1) (hb : d112688 p = 1) : d114342 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d112688 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d7327 q = 1) (hb : d112688 q = 1) : d114188 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d7327, d114188, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18299 q ha hb
    | true =>
      simp only [d7327, d114188, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d7328 q = 1) (hb : d112688 q = 1) : d114189 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d7328, d114189, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7328, d114189, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d7483 q = 1) (hb : d112688 q = 1) : d114320 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d7483, d114320, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d7483, d114320, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d7484 q = 1) (hb : d112688 q = 1) : d114321 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d7484, d114321, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d7484, d114321, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d7485 q = 1) (hb : d112688 q = 1) : d114322 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d7485, d114322, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d7485, d114322, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d7507 q = 1) (hb : d112688 q = 1) : d114342 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d7507, d114342, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d7507, d114342, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro18343 (p : Pattern) (ha : d85476 p = 1) (hb : d112688 p = 1) : d114348 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d112688 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d7454 q = 1) (hb : d112688 q = 1) : d114296 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7454, d114296, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18330 q ha hb
    | true =>
      simp only [d7454, d114296, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18328 q ha hb
  have h2 (q : Pattern) (ha : d7455 q = 1) (hb : d112688 q = 1) : d114297 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d7455, d114297, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7455, d114297, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d7456 q = 1) (hb : d112688 q = 1) : d114298 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d7456, d114298, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d7456, d114298, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d7457 q = 1) (hb : d112688 q = 1) : d114299 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d7457, d114299, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7457, d114299, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d7461 q = 1) (hb : d112688 q = 1) : d114303 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7461, d114303, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18331 q ha hb
    | true =>
      simp only [d7461, d114303, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18329 q ha hb
  have h6 (q : Pattern) (ha : d7462 q = 1) (hb : d112688 q = 1) : d114304 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d7462, d114304, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7462, d114304, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d7463 q = 1) (hb : d112688 q = 1) : d114305 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d7463, d114305, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d7463, d114305, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d7472 q = 1) (hb : d112688 q = 1) : d114318 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7472, d114318, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18334 q ha hb
    | true =>
      simp only [d7472, d114318, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18323 q ha hb
  have h9 (q : Pattern) (ha : d85467 q = 1) (hb : d112688 q = 1) : d114319 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d85467, d114319, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d85467, d114319, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d7487 q = 1) (hb : d112688 q = 1) : d114324 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7487, d114324, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18335 q ha hb
    | true =>
      simp only [d7487, d114324, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d7488 q = 1) (hb : d112688 q = 1) : d114325 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d7488, d114325, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d7488, d114325, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d85468 q = 1) (hb : d112688 q = 1) : d114326 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d85468, d114326, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d85468, d114326, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d85469 q = 1) (hb : d112688 q = 1) : d114327 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d85469, d114327, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d85469, d114327, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d85470 q = 1) (hb : d112688 q = 1) : d114328 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d85470, d114328, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d85470, d114328, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d7494 q = 1) (hb : d112688 q = 1) : d114331 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7494, d114331, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18339 q ha hb
    | true =>
      simp only [d7494, d114331, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18337 q ha hb
  have h16 (q : Pattern) (ha : d7495 q = 1) (hb : d112688 q = 1) : d114332 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d7495, d114332, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7495, d114332, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d7496 q = 1) (hb : d112688 q = 1) : d114333 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d7496, d114333, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d7496, d114333, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h18 (q : Pattern) (ha : d7497 q = 1) (hb : d112688 q = 1) : d114334 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d7497, d114334, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7497, d114334, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d7499 q = 1) (hb : d112688 q = 1) : d114336 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7499, d114336, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18340 q ha hb
    | true =>
      simp only [d7499, d114336, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18338 q ha hb
  have h20 (q : Pattern) (ha : d7500 q = 1) (hb : d112688 q = 1) : d114337 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d7500, d114337, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7500, d114337, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
  have h21 (q : Pattern) (ha : d7501 q = 1) (hb : d112688 q = 1) : d114338 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d7501, d114338, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d7501, d114338, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h22 (q : Pattern) (ha : d7503 q = 1) (hb : d112688 q = 1) : d114340 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7503, d114340, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18341 q ha hb
    | true =>
      simp only [d7503, d114340, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18325 q ha hb
  have h23 (q : Pattern) (ha : d85472 q = 1) (hb : d112688 q = 1) : d114341 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d85472, d114341, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
    | true =>
      simp only [d85472, d114341, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h24 (q : Pattern) (ha : d7508 q = 1) (hb : d112688 q = 1) : d114343 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7508, d114343, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18342 q ha hb
    | true =>
      simp only [d7508, d114343, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h25 (q : Pattern) (ha : d7509 q = 1) (hb : d112688 q = 1) : d114344 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d7509, d114344, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q ha hb
    | true =>
      simp only [d7509, d114344, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h26 (q : Pattern) (ha : d85473 q = 1) (hb : d112688 q = 1) : d114345 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d85473, d114345, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
    | true =>
      simp only [d85473, d114345, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q ha hb
  have h27 (q : Pattern) (ha : d85474 q = 1) (hb : d112688 q = 1) : d114346 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d85474, d114346, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d85474, d114346, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h26 q ha hb
  have h28 (q : Pattern) (ha : d85475 q = 1) (hb : d112688 q = 1) : d114347 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d85475, d114347, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d85475, d114347, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h27 q ha hb
  have h29 (q : Pattern) (ha : d85476 q = 1) (hb : d112688 q = 1) : d114348 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d85476, d114348, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d85476, d114348, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h28 q ha hb
  exact h29 p ha hb
theorem andIntro18344 (p : Pattern) (ha : d85483 p = 1) (hb : d112688 p = 1) : d114357 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d112688 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d7503 q = 1) (hb : d112688 q = 1) : d114340 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7503, d114340, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18341 q ha hb
    | true =>
      simp only [d7503, d114340, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18325 q ha hb
  have h2 (q : Pattern) (ha : d85472 q = 1) (hb : d112688 q = 1) : d114341 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d85472, d114341, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d85472, d114341, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d7508 q = 1) (hb : d112688 q = 1) : d114343 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7508, d114343, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18342 q ha hb
    | true =>
      simp only [d7508, d114343, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d7509 q = 1) (hb : d112688 q = 1) : d114344 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d7509, d114344, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d7509, d114344, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d85473 q = 1) (hb : d112688 q = 1) : d114345 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d85473, d114345, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d85473, d114345, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d85481 q = 1) (hb : d112688 q = 1) : d114355 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d85481, d114355, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d85481, d114355, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d85482 q = 1) (hb : d112688 q = 1) : d114356 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d85482, d114356, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d85482, d114356, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d85483 q = 1) (hb : d112688 q = 1) : d114357 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d85483, d114357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d85483, d114357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro18345 (p : Pattern) (ha : d664 p = 1) (hb : d94753 p = 1) : d12595 p = 1 := by
  have h0 (q : Pattern) (ha : d1 q = 1) (hb : d663 q = 1) : d663 q = 1 := by
    exact hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d416 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d664 q = 1) (hb : d94753 q = 1) : d12595 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d664, d94753, d12595, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d664, d94753, d12595, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  exact h2 p ha hb
theorem andIntro18346 (p : Pattern) (ha : d7529 p = 1) (hb : d112688 p = 1) : d114368 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d94753 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d665 q = 1) (hb : d94753 q = 1) : d12596 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d665, d12596, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18345 q ha hb
    | true =>
      simp only [d665, d12596, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12479 q ha hb
  have h2 (q : Pattern) (ha : d666 q = 1) (hb : d94753 q = 1) : d12597 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d666, d12597, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d666, d12597, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d667 q = 1) (hb : d94753 q = 1) : d12598 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d667, d12598, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d667, d12598, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d112686 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d231 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d418 q = 1) (hb : d112686 q = 1) : d114363 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d418, d112686, d114363, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12479 q ha hb
    | true =>
      simp only [d418, d112686, d114363, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d419 q = 1) (hb : d112686 q = 1) : d114364 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d419, d114364, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d419, d114364, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d420 q = 1) (hb : d112686 q = 1) : d114365 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d420, d114365, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d420, d114365, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d668 q = 1) (hb : d112687 q = 1) : d114366 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d668, d112687, d114366, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d668, d112687, d114366, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d7528 q = 1) (hb : d112688 q = 1) : d114367 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d7528, d112688, d114367, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d7528, d112688, d114367, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d112688 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d7529 q = 1) (hb : d112688 q = 1) : d114368 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d7529, d114368, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d7529, d114368, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  exact h13 p ha hb
theorem andIntro18347 (p : Pattern) (ha : d7535 p = 1) (hb : d112688 p = 1) : d114374 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d112688 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d7530 q = 1) (hb : d112688 q = 1) : d114369 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d7530, d114369, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18346 q ha hb
    | true =>
      simp only [d7530, d114369, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d7531 q = 1) (hb : d112688 q = 1) : d114370 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d7531, d114370, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7531, d114370, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d7391 q = 1) (hb : d112688 q = 1) : d114242 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d7391, d114242, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18309 q ha hb
    | true =>
      simp only [d7391, d114242, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d7392 q = 1) (hb : d112688 q = 1) : d114243 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d7392, d114243, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7392, d114243, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d7532 q = 1) (hb : d112688 q = 1) : d114371 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d7532, d114371, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d7532, d114371, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d7533 q = 1) (hb : d112688 q = 1) : d114372 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d7533, d114372, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d7533, d114372, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d7534 q = 1) (hb : d112688 q = 1) : d114373 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d7534, d114373, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d7534, d114373, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d7535 q = 1) (hb : d112688 q = 1) : d114374 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d7535, d114374, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d7535, d114374, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro18348 (p : Pattern) (ha : d7539 p = 1) (hb : d112688 p = 1) : d114378 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d112688 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d7391 q = 1) (hb : d112688 q = 1) : d114242 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d7391, d114242, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18309 q ha hb
    | true =>
      simp only [d7391, d114242, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d7392 q = 1) (hb : d112688 q = 1) : d114243 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d7392, d114243, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7392, d114243, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d684 q = 1) (hb : d112688 q = 1) : d12623 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d684, d12623, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18320 q ha hb
    | true =>
      simp only [d684, d12623, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d685 q = 1) (hb : d112688 q = 1) : d12624 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d685, d12624, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d685, d12624, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d7536 q = 1) (hb : d112688 q = 1) : d114375 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d7536, d114375, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d7536, d114375, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d7537 q = 1) (hb : d112688 q = 1) : d114376 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d7537, d114376, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d7537, d114376, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d7538 q = 1) (hb : d112688 q = 1) : d114377 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d7538, d114377, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d7538, d114377, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d7539 q = 1) (hb : d112688 q = 1) : d114378 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d7539, d114378, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d7539, d114378, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro18349 (p : Pattern) (ha : d7554 p = 1) (hb : d112688 p = 1) : d114384 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d112688 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d7391 q = 1) (hb : d112688 q = 1) : d114242 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d7391, d114242, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18309 q ha hb
    | true =>
      simp only [d7391, d114242, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d7392 q = 1) (hb : d112688 q = 1) : d114243 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d7392, d114243, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7392, d114243, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d7551 q = 1) (hb : d112688 q = 1) : d114381 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d7551, d114381, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d7551, d114381, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d7552 q = 1) (hb : d112688 q = 1) : d114382 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d7552, d114382, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d7552, d114382, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d7553 q = 1) (hb : d112688 q = 1) : d114383 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d7553, d114383, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d7553, d114383, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d7554 q = 1) (hb : d112688 q = 1) : d114384 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d7554, d114384, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d7554, d114384, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro18350 (p : Pattern) (ha : d85493 p = 1) (hb : d112688 p = 1) : d114390 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d112688 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d7540 q = 1) (hb : d112688 q = 1) : d114379 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7540, d114379, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18347 q ha hb
    | true =>
      simp only [d7540, d114379, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18348 q ha hb
  have h2 (q : Pattern) (ha : d85489 q = 1) (hb : d112688 q = 1) : d114380 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d85489, d114380, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d85489, d114380, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d7555 q = 1) (hb : d112688 q = 1) : d114385 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7555, d114385, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18349 q ha hb
    | true =>
      simp only [d7555, d114385, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d7556 q = 1) (hb : d112688 q = 1) : d114386 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d7556, d114386, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d7556, d114386, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d85490 q = 1) (hb : d112688 q = 1) : d114387 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d85490, d114387, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d85490, d114387, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d85491 q = 1) (hb : d112688 q = 1) : d114388 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d85491, d114388, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d85491, d114388, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d85492 q = 1) (hb : d112688 q = 1) : d114389 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d85492, d114389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d85492, d114389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d85493 q = 1) (hb : d112688 q = 1) : d114390 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d85493, d114390, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d85493, d114390, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro18351 (p : Pattern) (ha : d85499 p = 1) (hb : d112688 p = 1) : d114396 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d112688 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d7440 q = 1) (hb : d112688 q = 1) : d114282 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d7440, d114282, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7440, d114282, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18324 q ha hb
  have h2 (q : Pattern) (ha : d7441 q = 1) (hb : d112688 q = 1) : d114283 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d7441, d114283, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d7441, d114283, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d7449 q = 1) (hb : d112688 q = 1) : d114291 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d7449, d114291, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18324 q ha hb
    | true =>
      simp only [d7449, d114291, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18326 q ha hb
  have h4 (q : Pattern) (ha : d7450 q = 1) (hb : d112688 q = 1) : d114292 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d7450, d114292, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d7450, d114292, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d7451 q = 1) (hb : d112688 q = 1) : d114293 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d7451, d114293, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d7451, d114293, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d85477 q = 1) (hb : d112688 q = 1) : d114349 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d85477, d114349, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18336 q ha hb
    | true =>
      simp only [d85477, d114349, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18343 q ha hb
  have h7 (q : Pattern) (ha : d7516 q = 1) (hb : d112688 q = 1) : d114351 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d7516, d114351, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18327 q ha hb
    | true =>
      simp only [d7516, d114351, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18318 q ha hb
  have h8 (q : Pattern) (ha : d85478 q = 1) (hb : d112688 q = 1) : d114352 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d85478, d114352, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d85478, d114352, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d85479 q = 1) (hb : d112688 q = 1) : d114353 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d85479, d114353, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d85479, d114353, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d85480 q = 1) (hb : d112688 q = 1) : d114354 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d85480, d114354, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d85480, d114354, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d85484 q = 1) (hb : d112688 q = 1) : d114358 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d85484, d114358, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d85484, d114358, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18344 q ha hb
  have h12 (q : Pattern) (ha : d654 q = 1) (hb : d112688 q = 1) : d12590 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d654, d12590, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d654, d12590, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18319 q ha hb
  have h13 (q : Pattern) (ha : d85485 q = 1) (hb : d112688 q = 1) : d114359 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d85485, d114359, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d85485, d114359, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d85486 q = 1) (hb : d112688 q = 1) : d114360 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d85486, d114360, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d85486, d114360, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d85487 q = 1) (hb : d112688 q = 1) : d114361 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d85487, d114361, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d85487, d114361, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h16 (q : Pattern) (ha : d85488 q = 1) (hb : d112688 q = 1) : d114362 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d85488, d114362, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d85488, d114362, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d85494 q = 1) (hb : d112688 q = 1) : d114391 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d85494, d114391, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d85494, d114391, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18350 q ha hb
  have h18 (q : Pattern) (ha : d737 q = 1) (hb : d112688 q = 1) : d12675 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d737, d12675, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d737, d12675, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18322 q ha hb
  have h19 (q : Pattern) (ha : d85495 q = 1) (hb : d112688 q = 1) : d114392 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d85495, d114392, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d85495, d114392, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d85496 q = 1) (hb : d112688 q = 1) : d114393 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d85496, d114393, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d85496, d114393, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h21 (q : Pattern) (ha : d85497 q = 1) (hb : d112688 q = 1) : d114394 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d85497, d114394, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d85497, d114394, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h22 (q : Pattern) (ha : d85498 q = 1) (hb : d112688 q = 1) : d114395 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d85498, d114395, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d85498, d114395, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h23 (q : Pattern) (ha : d85499 q = 1) (hb : d112688 q = 1) : d114396 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d85499, d114396, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d85499, d114396, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
  exact h23 p ha hb
theorem andIntro18352 (p : Pattern) (ha : d85505 p = 1) (hb : d112688 p = 1) : d114402 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d112688 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d85500 q = 1) (hb : d112688 q = 1) : d114397 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d85500, d114397, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d85500, d114397, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18351 q ha hb
  have h2 (q : Pattern) (ha : d85501 q = 1) (hb : d112688 q = 1) : d114398 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d85501, d114398, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d85501, d114398, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d85502 q = 1) (hb : d112688 q = 1) : d114399 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d85502, d114399, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d85502, d114399, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d85503 q = 1) (hb : d112688 q = 1) : d114400 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d85503, d114400, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d85503, d114400, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d85504 q = 1) (hb : d112688 q = 1) : d114401 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d85504, d114401, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d85504, d114401, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d85505 q = 1) (hb : d112688 q = 1) : d114402 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d85505, d114402, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d85505, d114402, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro18353 (p : Pattern) (ha : d773 p = 1) (hb : d112688 p = 1) : d12697 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d94753 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d762 q = 1) (hb : d94753 q = 1) : d762 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d763 q = 1) (hb : d94753 q = 1) : d4914 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d763, d4914, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12488 q ha hb
    | true =>
      simp only [d763, d4914, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d764 q = 1) (hb : d94753 q = 1) : d4915 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d764, d4915, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d764, d4915, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d765 q = 1) (hb : d94753 q = 1) : d4916 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d765, d4916, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d765, d4916, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d112686 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d767 q = 1) (hb : d112687 q = 1) : d4917 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d767, d112687, d4917, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d767, d112687, d4917, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d772 q = 1) (hb : d112688 q = 1) : d12696 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d772, d112688, d12696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d772, d112688, d12696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d112688 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d773 q = 1) (hb : d112688 q = 1) : d12697 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d773, d12697, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d773, d12697, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro18354 (p : Pattern) (ha : d783 p = 1) (hb : d112688 p = 1) : d12707 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d112688 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d774 q = 1) (hb : d112688 q = 1) : d12698 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d774, d12698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18353 q ha hb
    | true =>
      simp only [d774, d12698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d775 q = 1) (hb : d112688 q = 1) : d12699 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d775, d12699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d775, d12699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d780 q = 1) (hb : d112688 q = 1) : d12704 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d780, d12704, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d780, d12704, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d781 q = 1) (hb : d112688 q = 1) : d12705 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d781, d12705, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d781, d12705, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d782 q = 1) (hb : d112688 q = 1) : d12706 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d782, d12706, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d782, d12706, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d783 q = 1) (hb : d112688 q = 1) : d12707 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d783, d12707, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d783, d12707, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro18355 (p : Pattern) (ha : d793 p = 1) (hb : d112688 p = 1) : d12717 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d112688 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d774 q = 1) (hb : d112688 q = 1) : d12698 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d774, d12698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18353 q ha hb
    | true =>
      simp only [d774, d12698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d775 q = 1) (hb : d112688 q = 1) : d12699 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d775, d12699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d775, d12699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d780 q = 1) (hb : d112688 q = 1) : d12704 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d780, d12704, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d780, d12704, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d781 q = 1) (hb : d112688 q = 1) : d12705 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d781, d12705, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d781, d12705, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d782 q = 1) (hb : d112688 q = 1) : d12706 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d782, d12706, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d782, d12706, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d793 q = 1) (hb : d112688 q = 1) : d12717 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d793, d12717, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d793, d12717, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro18356 (p : Pattern) (ha : d950 p = 1) (hb : d112688 p = 1) : d12839 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d112688 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d939 q = 1) (hb : d112688 q = 1) : d12828 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d939, d12828, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18354 q ha hb
    | true =>
      simp only [d939, d12828, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d940 q = 1) (hb : d112688 q = 1) : d12829 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d940, d12829, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d940, d12829, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d941 q = 1) (hb : d112688 q = 1) : d12830 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d941, d12830, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d941, d12830, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d942 q = 1) (hb : d112688 q = 1) : d12831 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d942, d12831, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d942, d12831, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d943 q = 1) (hb : d112688 q = 1) : d12832 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d943, d12832, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d943, d12832, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d945 q = 1) (hb : d112688 q = 1) : d12834 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d945, d12834, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18355 q ha hb
    | true =>
      simp only [d945, d12834, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d946 q = 1) (hb : d112688 q = 1) : d12835 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d946, d12835, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d946, d12835, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d947 q = 1) (hb : d112688 q = 1) : d12836 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d947, d12836, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d947, d12836, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d948 q = 1) (hb : d112688 q = 1) : d12837 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d948, d12837, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d948, d12837, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d949 q = 1) (hb : d112688 q = 1) : d12838 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d949, d12838, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d949, d12838, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d950 q = 1) (hb : d112688 q = 1) : d12839 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d950, d12839, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d950, d12839, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro18357 (p : Pattern) (ha : d959 p = 1) (hb : d112688 p = 1) : d12848 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d112688 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d945 q = 1) (hb : d112688 q = 1) : d12834 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d945, d12834, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18355 q ha hb
    | true =>
      simp only [d945, d12834, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d946 q = 1) (hb : d112688 q = 1) : d12835 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d946, d12835, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d946, d12835, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d947 q = 1) (hb : d112688 q = 1) : d12836 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d947, d12836, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d947, d12836, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d948 q = 1) (hb : d112688 q = 1) : d12837 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d948, d12837, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d948, d12837, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d949 q = 1) (hb : d112688 q = 1) : d12838 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d949, d12838, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d949, d12838, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d959 q = 1) (hb : d112688 q = 1) : d12848 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d959, d12848, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d959, d12848, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro18358 (p : Pattern) (ha : d1005 p = 1) (hb : d112688 p = 1) : d12885 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d94753 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d986 q = 1) (hb : d94753 q = 1) : d986 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d987 q = 1) (hb : d94753 q = 1) : d6211 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d987, d6211, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12524 q ha hb
    | true =>
      simp only [d987, d6211, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d988 q = 1) (hb : d94753 q = 1) : d6212 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d988, d6212, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d988, d6212, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d989 q = 1) (hb : d94753 q = 1) : d6213 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d989, d6213, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d989, d6213, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d112686 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d995 q = 1) (hb : d112687 q = 1) : d6214 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d995, d112687, d6214, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d995, d112687, d6214, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d1004 q = 1) (hb : d112688 q = 1) : d12884 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d1004, d112688, d12884, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d1004, d112688, d12884, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d112688 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d1005 q = 1) (hb : d112688 q = 1) : d12885 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d1005, d12885, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d1005, d12885, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro18359 (p : Pattern) (ha : d1063 p = 1) (hb : d112688 p = 1) : d12935 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d112688 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1006 q = 1) (hb : d112688 q = 1) : d12886 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d1006, d12886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18358 q ha hb
    | true =>
      simp only [d1006, d12886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d1007 q = 1) (hb : d112688 q = 1) : d12887 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d1007, d12887, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1007, d12887, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d1060 q = 1) (hb : d112688 q = 1) : d12932 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d1060, d12932, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d1060, d12932, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d1061 q = 1) (hb : d112688 q = 1) : d12933 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d1061, d12933, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d1061, d12933, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d1062 q = 1) (hb : d112688 q = 1) : d12934 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d1062, d12934, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d1062, d12934, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d1063 q = 1) (hb : d112688 q = 1) : d12935 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d1063, d12935, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d1063, d12935, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro18360 (p : Pattern) (ha : d1069 p = 1) (hb : d112688 p = 1) : d12941 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d112688 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1064 q = 1) (hb : d112688 q = 1) : d12936 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d1064, d12936, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18359 q ha hb
    | true =>
      simp only [d1064, d12936, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d1065 q = 1) (hb : d112688 q = 1) : d12937 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d1065, d12937, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1065, d12937, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d1066 q = 1) (hb : d112688 q = 1) : d12938 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d1066, d12938, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d1066, d12938, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d1067 q = 1) (hb : d112688 q = 1) : d12939 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d1067, d12939, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1067, d12939, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d1068 q = 1) (hb : d112688 q = 1) : d12940 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d1068, d12940, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1068, d12940, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d1069 q = 1) (hb : d112688 q = 1) : d12941 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d1069, d12941, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1069, d12941, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro18361 (p : Pattern) (ha : d7575 p = 1) (hb : d112688 p = 1) : d114406 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d94753 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d759 q = 1) (hb : d94753 q = 1) : d12688 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d759, d12688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12510 q ha hb
    | true =>
      simp only [d759, d12688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12488 q ha hb
  have h2 (q : Pattern) (ha : d760 q = 1) (hb : d94753 q = 1) : d12689 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d760, d12689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d760, d12689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d761 q = 1) (hb : d94753 q = 1) : d12690 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d761, d12690, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d761, d12690, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d112686 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d762 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d763 q = 1) (hb : d112686 q = 1) : d88489 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d763, d112686, d88489, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12488 q ha hb
    | true =>
      simp only [d763, d112686, d88489, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d764 q = 1) (hb : d112686 q = 1) : d88490 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d764, d88490, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d764, d88490, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d765 q = 1) (hb : d112686 q = 1) : d88491 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d765, d88491, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d765, d88491, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d766 q = 1) (hb : d112687 q = 1) : d114404 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d766, d112687, d114404, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d766, d112687, d114404, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d7574 q = 1) (hb : d112688 q = 1) : d114405 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d7574, d112688, d114405, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d7574, d112688, d114405, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d112688 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d7575 q = 1) (hb : d112688 q = 1) : d114406 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d7575, d114406, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d7575, d114406, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  exact h13 p ha hb
theorem andIntro18362 (p : Pattern) (ha : d7581 p = 1) (hb : d112688 p = 1) : d114412 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d112688 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d7576 q = 1) (hb : d112688 q = 1) : d114407 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d7576, d114407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18361 q ha hb
    | true =>
      simp only [d7576, d114407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d7577 q = 1) (hb : d112688 q = 1) : d114408 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d7577, d114408, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7577, d114408, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d774 q = 1) (hb : d112688 q = 1) : d12698 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d774, d12698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18353 q ha hb
    | true =>
      simp only [d774, d12698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d775 q = 1) (hb : d112688 q = 1) : d12699 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d775, d12699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d775, d12699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d7578 q = 1) (hb : d112688 q = 1) : d114409 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d7578, d114409, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d7578, d114409, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d7579 q = 1) (hb : d112688 q = 1) : d114410 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d7579, d114410, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d7579, d114410, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d7580 q = 1) (hb : d112688 q = 1) : d114411 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d7580, d114411, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d7580, d114411, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d7581 q = 1) (hb : d112688 q = 1) : d114412 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d7581, d114412, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7581, d114412, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro18363 (p : Pattern) (ha : d7587 p = 1) (hb : d112688 p = 1) : d114418 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d112688 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d7582 q = 1) (hb : d112688 q = 1) : d114413 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7582, d114413, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18362 q ha hb
    | true =>
      simp only [d7582, d114413, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18354 q ha hb
  have h2 (q : Pattern) (ha : d7583 q = 1) (hb : d112688 q = 1) : d114414 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d7583, d114414, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7583, d114414, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d7584 q = 1) (hb : d112688 q = 1) : d114415 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d7584, d114415, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d7584, d114415, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d7585 q = 1) (hb : d112688 q = 1) : d114416 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d7585, d114416, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7585, d114416, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d7586 q = 1) (hb : d112688 q = 1) : d114417 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d7586, d114417, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7586, d114417, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d7587 q = 1) (hb : d112688 q = 1) : d114418 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d7587, d114418, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7587, d114418, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro18364 (p : Pattern) (ha : d7590 p = 1) (hb : d112688 p = 1) : d114421 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d112688 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d7576 q = 1) (hb : d112688 q = 1) : d114407 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d7576, d114407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18361 q ha hb
    | true =>
      simp only [d7576, d114407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d7577 q = 1) (hb : d112688 q = 1) : d114408 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d7577, d114408, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7577, d114408, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d774 q = 1) (hb : d112688 q = 1) : d12698 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d774, d12698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18353 q ha hb
    | true =>
      simp only [d774, d12698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d775 q = 1) (hb : d112688 q = 1) : d12699 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d775, d12699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d775, d12699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d7578 q = 1) (hb : d112688 q = 1) : d114409 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d7578, d114409, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d7578, d114409, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d7579 q = 1) (hb : d112688 q = 1) : d114410 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d7579, d114410, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d7579, d114410, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d7580 q = 1) (hb : d112688 q = 1) : d114411 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d7580, d114411, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d7580, d114411, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d7590 q = 1) (hb : d112688 q = 1) : d114421 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d7590, d114421, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d7590, d114421, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro18365 (p : Pattern) (ha : d7596 p = 1) (hb : d112688 p = 1) : d114427 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d112688 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d7582 q = 1) (hb : d112688 q = 1) : d114413 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7582, d114413, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18362 q ha hb
    | true =>
      simp only [d7582, d114413, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18354 q ha hb
  have h2 (q : Pattern) (ha : d7583 q = 1) (hb : d112688 q = 1) : d114414 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d7583, d114414, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7583, d114414, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d7584 q = 1) (hb : d112688 q = 1) : d114415 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d7584, d114415, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d7584, d114415, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d7585 q = 1) (hb : d112688 q = 1) : d114416 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d7585, d114416, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7585, d114416, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d7586 q = 1) (hb : d112688 q = 1) : d114417 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d7586, d114417, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7586, d114417, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d7591 q = 1) (hb : d112688 q = 1) : d114422 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7591, d114422, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18364 q ha hb
    | true =>
      simp only [d7591, d114422, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18355 q ha hb
  have h7 (q : Pattern) (ha : d7592 q = 1) (hb : d112688 q = 1) : d114423 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d7592, d114423, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7592, d114423, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d7593 q = 1) (hb : d112688 q = 1) : d114424 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d7593, d114424, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d7593, d114424, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d7594 q = 1) (hb : d112688 q = 1) : d114425 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d7594, d114425, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7594, d114425, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d7595 q = 1) (hb : d112688 q = 1) : d114426 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d7595, d114426, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7595, d114426, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d7596 q = 1) (hb : d112688 q = 1) : d114427 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d7596, d114427, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d7596, d114427, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro18366 (p : Pattern) (ha : d7663 p = 1) (hb : d112688 p = 1) : d114487 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d112688 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d7582 q = 1) (hb : d112688 q = 1) : d114413 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7582, d114413, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18362 q ha hb
    | true =>
      simp only [d7582, d114413, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18354 q ha hb
  have h2 (q : Pattern) (ha : d7583 q = 1) (hb : d112688 q = 1) : d114414 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d7583, d114414, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7583, d114414, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d7584 q = 1) (hb : d112688 q = 1) : d114415 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d7584, d114415, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d7584, d114415, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d7585 q = 1) (hb : d112688 q = 1) : d114416 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d7585, d114416, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7585, d114416, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d7586 q = 1) (hb : d112688 q = 1) : d114417 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d7586, d114417, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7586, d114417, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d939 q = 1) (hb : d112688 q = 1) : d12828 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d939, d12828, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18354 q ha hb
    | true =>
      simp only [d939, d12828, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d940 q = 1) (hb : d112688 q = 1) : d12829 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d940, d12829, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d940, d12829, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d941 q = 1) (hb : d112688 q = 1) : d12830 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d941, d12830, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d941, d12830, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d942 q = 1) (hb : d112688 q = 1) : d12831 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d942, d12831, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d942, d12831, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d943 q = 1) (hb : d112688 q = 1) : d12832 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d943, d12832, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d943, d12832, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d7663 q = 1) (hb : d112688 q = 1) : d114487 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d7663, d114487, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d7663, d114487, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro18367 (p : Pattern) (ha : d806 p = 1) (hb : d112688 p = 1) : d12730 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d112688 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d774 q = 1) (hb : d112688 q = 1) : d12698 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d774, d12698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18353 q ha hb
    | true =>
      simp only [d774, d12698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d775 q = 1) (hb : d112688 q = 1) : d12699 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d775, d12699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d775, d12699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d780 q = 1) (hb : d112688 q = 1) : d12704 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d780, d12704, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d780, d12704, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d781 q = 1) (hb : d112688 q = 1) : d12705 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d781, d12705, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d781, d12705, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d805 q = 1) (hb : d112688 q = 1) : d12729 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d805, d12729, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d805, d12729, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d806 q = 1) (hb : d112688 q = 1) : d12730 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d806, d12730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d806, d12730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro18368 (p : Pattern) (ha : d816 p = 1) (hb : d112688 p = 1) : d12740 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d112688 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d774 q = 1) (hb : d112688 q = 1) : d12698 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d774, d12698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18353 q ha hb
    | true =>
      simp only [d774, d12698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d775 q = 1) (hb : d112688 q = 1) : d12699 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d775, d12699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d775, d12699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d780 q = 1) (hb : d112688 q = 1) : d12704 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d780, d12704, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d780, d12704, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d814 q = 1) (hb : d112688 q = 1) : d12738 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d814, d12738, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d814, d12738, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d815 q = 1) (hb : d112688 q = 1) : d12739 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d815, d12739, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d815, d12739, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d816 q = 1) (hb : d112688 q = 1) : d12740 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d816, d12740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d816, d12740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro18369 (p : Pattern) (ha : d7601 p = 1) (hb : d112688 p = 1) : d114432 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d112688 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d7576 q = 1) (hb : d112688 q = 1) : d114407 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d7576, d114407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18361 q ha hb
    | true =>
      simp only [d7576, d114407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d7577 q = 1) (hb : d112688 q = 1) : d114408 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d7577, d114408, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7577, d114408, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d774 q = 1) (hb : d112688 q = 1) : d12698 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d774, d12698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18353 q ha hb
    | true =>
      simp only [d774, d12698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d775 q = 1) (hb : d112688 q = 1) : d12699 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d775, d12699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d775, d12699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d7578 q = 1) (hb : d112688 q = 1) : d114409 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d7578, d114409, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d7578, d114409, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d7579 q = 1) (hb : d112688 q = 1) : d114410 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d7579, d114410, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d7579, d114410, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d7600 q = 1) (hb : d112688 q = 1) : d114431 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d7600, d114431, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7600, d114431, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d7601 q = 1) (hb : d112688 q = 1) : d114432 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d7601, d114432, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7601, d114432, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro18370 (p : Pattern) (ha : d7608 p = 1) (hb : d112688 p = 1) : d114439 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d112688 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d7576 q = 1) (hb : d112688 q = 1) : d114407 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d7576, d114407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18361 q ha hb
    | true =>
      simp only [d7576, d114407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d7577 q = 1) (hb : d112688 q = 1) : d114408 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d7577, d114408, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7577, d114408, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d774 q = 1) (hb : d112688 q = 1) : d12698 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d774, d12698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18353 q ha hb
    | true =>
      simp only [d774, d12698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d775 q = 1) (hb : d112688 q = 1) : d12699 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d775, d12699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d775, d12699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d7578 q = 1) (hb : d112688 q = 1) : d114409 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d7578, d114409, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d7578, d114409, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d7606 q = 1) (hb : d112688 q = 1) : d114437 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d7606, d114437, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7606, d114437, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d7607 q = 1) (hb : d112688 q = 1) : d114438 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d7607, d114438, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d7607, d114438, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d7608 q = 1) (hb : d112688 q = 1) : d114439 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d7608, d114439, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7608, d114439, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro18371 (p : Pattern) (ha : d839 p = 1) (hb : d94753 p = 1) : d12744 p = 1 := by
  have h0 (q : Pattern) (ha : d1 q = 1) (hb : d838 q = 1) : d838 q = 1 := by
    exact hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d547 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d839 q = 1) (hb : d94753 q = 1) : d12744 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d839, d94753, d12744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d839, d94753, d12744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  exact h2 p ha hb
theorem andIntro18372 (p : Pattern) (ha : d7613 p = 1) (hb : d112688 p = 1) : d114448 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d94753 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d840 q = 1) (hb : d94753 q = 1) : d12745 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d840, d12745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18371 q ha hb
    | true =>
      simp only [d840, d12745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12510 q ha hb
  have h2 (q : Pattern) (ha : d841 q = 1) (hb : d94753 q = 1) : d12746 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d841, d12746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d841, d12746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d842 q = 1) (hb : d94753 q = 1) : d12747 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d842, d12747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d842, d12747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d112686 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d758 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d759 q = 1) (hb : d112686 q = 1) : d114443 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d759, d112686, d114443, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12510 q ha hb
    | true =>
      simp only [d759, d112686, d114443, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d760 q = 1) (hb : d112686 q = 1) : d114444 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d760, d114444, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d760, d114444, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d761 q = 1) (hb : d112686 q = 1) : d114445 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d761, d114445, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d761, d114445, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d843 q = 1) (hb : d112687 q = 1) : d114446 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d843, d112687, d114446, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d843, d112687, d114446, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d7612 q = 1) (hb : d112688 q = 1) : d114447 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d7612, d112688, d114447, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d7612, d112688, d114447, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d112688 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d7613 q = 1) (hb : d112688 q = 1) : d114448 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d7613, d114448, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d7613, d114448, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  exact h13 p ha hb
theorem andIntro18373 (p : Pattern) (ha : d7619 p = 1) (hb : d112688 p = 1) : d114454 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d112688 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d7614 q = 1) (hb : d112688 q = 1) : d114449 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d7614, d114449, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18372 q ha hb
    | true =>
      simp only [d7614, d114449, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d7615 q = 1) (hb : d112688 q = 1) : d114450 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d7615, d114450, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7615, d114450, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d7576 q = 1) (hb : d112688 q = 1) : d114407 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d7576, d114407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18361 q ha hb
    | true =>
      simp only [d7576, d114407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d7577 q = 1) (hb : d112688 q = 1) : d114408 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d7577, d114408, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7577, d114408, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d7616 q = 1) (hb : d112688 q = 1) : d114451 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d7616, d114451, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d7616, d114451, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d7617 q = 1) (hb : d112688 q = 1) : d114452 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d7617, d114452, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d7617, d114452, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d7618 q = 1) (hb : d112688 q = 1) : d114453 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d7618, d114453, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d7618, d114453, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d7619 q = 1) (hb : d112688 q = 1) : d114454 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d7619, d114454, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7619, d114454, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro18374 (p : Pattern) (ha : d7634 p = 1) (hb : d112688 p = 1) : d114460 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d112688 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d7576 q = 1) (hb : d112688 q = 1) : d114407 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d7576, d114407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18361 q ha hb
    | true =>
      simp only [d7576, d114407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d7577 q = 1) (hb : d112688 q = 1) : d114408 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d7577, d114408, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7577, d114408, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d7631 q = 1) (hb : d112688 q = 1) : d114457 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d7631, d114457, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d7631, d114457, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d7632 q = 1) (hb : d112688 q = 1) : d114458 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d7632, d114458, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d7632, d114458, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d7633 q = 1) (hb : d112688 q = 1) : d114459 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d7633, d114459, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d7633, d114459, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d7634 q = 1) (hb : d112688 q = 1) : d114460 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d7634, d114460, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7634, d114460, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro18375 (p : Pattern) (ha : d85511 p = 1) (hb : d112688 p = 1) : d114466 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d112688 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d7602 q = 1) (hb : d112688 q = 1) : d114433 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7602, d114433, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18369 q ha hb
    | true =>
      simp only [d7602, d114433, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18367 q ha hb
  have h2 (q : Pattern) (ha : d7603 q = 1) (hb : d112688 q = 1) : d114434 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d7603, d114434, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7603, d114434, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d7604 q = 1) (hb : d112688 q = 1) : d114435 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d7604, d114435, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d7604, d114435, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d7605 q = 1) (hb : d112688 q = 1) : d114436 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d7605, d114436, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7605, d114436, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d7609 q = 1) (hb : d112688 q = 1) : d114440 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7609, d114440, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18370 q ha hb
    | true =>
      simp only [d7609, d114440, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18368 q ha hb
  have h6 (q : Pattern) (ha : d7610 q = 1) (hb : d112688 q = 1) : d114441 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d7610, d114441, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7610, d114441, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d7611 q = 1) (hb : d112688 q = 1) : d114442 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d7611, d114442, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d7611, d114442, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d7620 q = 1) (hb : d112688 q = 1) : d114455 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7620, d114455, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18373 q ha hb
    | true =>
      simp only [d7620, d114455, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18362 q ha hb
  have h9 (q : Pattern) (ha : d85507 q = 1) (hb : d112688 q = 1) : d114456 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d85507, d114456, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d85507, d114456, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d7635 q = 1) (hb : d112688 q = 1) : d114461 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7635, d114461, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18374 q ha hb
    | true =>
      simp only [d7635, d114461, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d7636 q = 1) (hb : d112688 q = 1) : d114462 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d7636, d114462, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d7636, d114462, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d85508 q = 1) (hb : d112688 q = 1) : d114463 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d85508, d114463, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d85508, d114463, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d85509 q = 1) (hb : d112688 q = 1) : d114464 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d85509, d114464, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d85509, d114464, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d85510 q = 1) (hb : d112688 q = 1) : d114465 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d85510, d114465, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d85510, d114465, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d85511 q = 1) (hb : d112688 q = 1) : d114466 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d85511, d114466, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d85511, d114466, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro18376 (p : Pattern) (ha : d916 p = 1) (hb : d112688 p = 1) : d12804 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d112688 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d774 q = 1) (hb : d112688 q = 1) : d12698 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d774, d12698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18353 q ha hb
    | true =>
      simp only [d774, d12698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d775 q = 1) (hb : d112688 q = 1) : d12699 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d775, d12699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d775, d12699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d780 q = 1) (hb : d112688 q = 1) : d12704 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d780, d12704, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d780, d12704, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d781 q = 1) (hb : d112688 q = 1) : d12705 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d781, d12705, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d781, d12705, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d805 q = 1) (hb : d112688 q = 1) : d12729 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d805, d12729, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d805, d12729, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d916 q = 1) (hb : d112688 q = 1) : d12804 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d916, d12804, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d916, d12804, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro18377 (p : Pattern) (ha : d922 p = 1) (hb : d112688 p = 1) : d12810 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d112688 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d774 q = 1) (hb : d112688 q = 1) : d12698 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d774, d12698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18353 q ha hb
    | true =>
      simp only [d774, d12698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d775 q = 1) (hb : d112688 q = 1) : d12699 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d775, d12699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d775, d12699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d780 q = 1) (hb : d112688 q = 1) : d12704 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d780, d12704, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d780, d12704, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d814 q = 1) (hb : d112688 q = 1) : d12738 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d814, d12738, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d814, d12738, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d815 q = 1) (hb : d112688 q = 1) : d12739 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d815, d12739, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d815, d12739, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d922 q = 1) (hb : d112688 q = 1) : d12810 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d922, d12810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d922, d12810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro18378 (p : Pattern) (ha : d7641 p = 1) (hb : d112688 p = 1) : d114467 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d112688 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d7576 q = 1) (hb : d112688 q = 1) : d114407 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d7576, d114407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18361 q ha hb
    | true =>
      simp only [d7576, d114407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d7577 q = 1) (hb : d112688 q = 1) : d114408 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d7577, d114408, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7577, d114408, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d774 q = 1) (hb : d112688 q = 1) : d12698 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d774, d12698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18353 q ha hb
    | true =>
      simp only [d774, d12698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d775 q = 1) (hb : d112688 q = 1) : d12699 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d775, d12699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d775, d12699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d7578 q = 1) (hb : d112688 q = 1) : d114409 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d7578, d114409, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d7578, d114409, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d7579 q = 1) (hb : d112688 q = 1) : d114410 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d7579, d114410, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d7579, d114410, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d7600 q = 1) (hb : d112688 q = 1) : d114431 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d7600, d114431, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7600, d114431, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d7641 q = 1) (hb : d112688 q = 1) : d114467 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d7641, d114467, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d7641, d114467, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro18379 (p : Pattern) (ha : d7646 p = 1) (hb : d112688 p = 1) : d114472 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d112688 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d7576 q = 1) (hb : d112688 q = 1) : d114407 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d7576, d114407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18361 q ha hb
    | true =>
      simp only [d7576, d114407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d7577 q = 1) (hb : d112688 q = 1) : d114408 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d7577, d114408, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7577, d114408, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d774 q = 1) (hb : d112688 q = 1) : d12698 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d774, d12698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18353 q ha hb
    | true =>
      simp only [d774, d12698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d775 q = 1) (hb : d112688 q = 1) : d12699 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d775, d12699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d775, d12699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d7578 q = 1) (hb : d112688 q = 1) : d114409 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d7578, d114409, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d7578, d114409, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d7606 q = 1) (hb : d112688 q = 1) : d114437 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d7606, d114437, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7606, d114437, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d7607 q = 1) (hb : d112688 q = 1) : d114438 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d7607, d114438, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d7607, d114438, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d7646 q = 1) (hb : d112688 q = 1) : d114472 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d7646, d114472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d7646, d114472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro18380 (p : Pattern) (ha : d7650 p = 1) (hb : d112688 p = 1) : d114476 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d112688 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d7614 q = 1) (hb : d112688 q = 1) : d114449 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d7614, d114449, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18372 q ha hb
    | true =>
      simp only [d7614, d114449, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d7615 q = 1) (hb : d112688 q = 1) : d114450 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d7615, d114450, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7615, d114450, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d7576 q = 1) (hb : d112688 q = 1) : d114407 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d7576, d114407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18361 q ha hb
    | true =>
      simp only [d7576, d114407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d7577 q = 1) (hb : d112688 q = 1) : d114408 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d7577, d114408, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7577, d114408, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d7616 q = 1) (hb : d112688 q = 1) : d114451 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d7616, d114451, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d7616, d114451, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d7617 q = 1) (hb : d112688 q = 1) : d114452 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d7617, d114452, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d7617, d114452, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d7618 q = 1) (hb : d112688 q = 1) : d114453 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d7618, d114453, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d7618, d114453, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d7650 q = 1) (hb : d112688 q = 1) : d114476 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d7650, d114476, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d7650, d114476, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro18381 (p : Pattern) (ha : d7655 p = 1) (hb : d112688 p = 1) : d114479 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d112688 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d7576 q = 1) (hb : d112688 q = 1) : d114407 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d7576, d114407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18361 q ha hb
    | true =>
      simp only [d7576, d114407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d7577 q = 1) (hb : d112688 q = 1) : d114408 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d7577, d114408, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7577, d114408, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d7631 q = 1) (hb : d112688 q = 1) : d114457 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d7631, d114457, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d7631, d114457, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d7632 q = 1) (hb : d112688 q = 1) : d114458 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d7632, d114458, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d7632, d114458, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d7633 q = 1) (hb : d112688 q = 1) : d114459 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d7633, d114459, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d7633, d114459, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d7655 q = 1) (hb : d112688 q = 1) : d114479 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d7655, d114479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d7655, d114479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro18382 (p : Pattern) (ha : d85516 p = 1) (hb : d112688 p = 1) : d114485 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d112688 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d7602 q = 1) (hb : d112688 q = 1) : d114433 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7602, d114433, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18369 q ha hb
    | true =>
      simp only [d7602, d114433, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18367 q ha hb
  have h2 (q : Pattern) (ha : d7603 q = 1) (hb : d112688 q = 1) : d114434 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d7603, d114434, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7603, d114434, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d7604 q = 1) (hb : d112688 q = 1) : d114435 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d7604, d114435, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d7604, d114435, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d7605 q = 1) (hb : d112688 q = 1) : d114436 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d7605, d114436, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7605, d114436, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d7609 q = 1) (hb : d112688 q = 1) : d114440 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7609, d114440, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18370 q ha hb
    | true =>
      simp only [d7609, d114440, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18368 q ha hb
  have h6 (q : Pattern) (ha : d7610 q = 1) (hb : d112688 q = 1) : d114441 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d7610, d114441, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7610, d114441, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d7611 q = 1) (hb : d112688 q = 1) : d114442 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d7611, d114442, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d7611, d114442, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d7620 q = 1) (hb : d112688 q = 1) : d114455 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7620, d114455, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18373 q ha hb
    | true =>
      simp only [d7620, d114455, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18362 q ha hb
  have h9 (q : Pattern) (ha : d85507 q = 1) (hb : d112688 q = 1) : d114456 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d85507, d114456, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d85507, d114456, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d7635 q = 1) (hb : d112688 q = 1) : d114461 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7635, d114461, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18374 q ha hb
    | true =>
      simp only [d7635, d114461, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d7636 q = 1) (hb : d112688 q = 1) : d114462 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d7636, d114462, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d7636, d114462, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d85508 q = 1) (hb : d112688 q = 1) : d114463 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d85508, d114463, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d85508, d114463, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d85509 q = 1) (hb : d112688 q = 1) : d114464 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d85509, d114464, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d85509, d114464, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d85510 q = 1) (hb : d112688 q = 1) : d114465 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d85510, d114465, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d85510, d114465, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d7642 q = 1) (hb : d112688 q = 1) : d114468 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7642, d114468, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18378 q ha hb
    | true =>
      simp only [d7642, d114468, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18376 q ha hb
  have h16 (q : Pattern) (ha : d7643 q = 1) (hb : d112688 q = 1) : d114469 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d7643, d114469, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7643, d114469, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d7644 q = 1) (hb : d112688 q = 1) : d114470 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d7644, d114470, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d7644, d114470, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h18 (q : Pattern) (ha : d7645 q = 1) (hb : d112688 q = 1) : d114471 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d7645, d114471, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7645, d114471, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d7647 q = 1) (hb : d112688 q = 1) : d114473 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7647, d114473, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18379 q ha hb
    | true =>
      simp only [d7647, d114473, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18377 q ha hb
  have h20 (q : Pattern) (ha : d7648 q = 1) (hb : d112688 q = 1) : d114474 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d7648, d114474, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7648, d114474, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
  have h21 (q : Pattern) (ha : d7649 q = 1) (hb : d112688 q = 1) : d114475 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d7649, d114475, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d7649, d114475, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h22 (q : Pattern) (ha : d7651 q = 1) (hb : d112688 q = 1) : d114477 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7651, d114477, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18380 q ha hb
    | true =>
      simp only [d7651, d114477, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18364 q ha hb
  have h23 (q : Pattern) (ha : d85512 q = 1) (hb : d112688 q = 1) : d114478 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d85512, d114478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
    | true =>
      simp only [d85512, d114478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h24 (q : Pattern) (ha : d7656 q = 1) (hb : d112688 q = 1) : d114480 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7656, d114480, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18381 q ha hb
    | true =>
      simp only [d7656, d114480, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h25 (q : Pattern) (ha : d7657 q = 1) (hb : d112688 q = 1) : d114481 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d7657, d114481, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q ha hb
    | true =>
      simp only [d7657, d114481, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h26 (q : Pattern) (ha : d85513 q = 1) (hb : d112688 q = 1) : d114482 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d85513, d114482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
    | true =>
      simp only [d85513, d114482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q ha hb
  have h27 (q : Pattern) (ha : d85514 q = 1) (hb : d112688 q = 1) : d114483 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d85514, d114483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d85514, d114483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h26 q ha hb
  have h28 (q : Pattern) (ha : d85515 q = 1) (hb : d112688 q = 1) : d114484 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d85515, d114484, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d85515, d114484, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h27 q ha hb
  have h29 (q : Pattern) (ha : d85516 q = 1) (hb : d112688 q = 1) : d114485 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d85516, d114485, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d85516, d114485, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h28 q ha hb
  exact h29 p ha hb
theorem andIntro18383 (p : Pattern) (ha : d85523 p = 1) (hb : d112688 p = 1) : d114494 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d112688 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d7651 q = 1) (hb : d112688 q = 1) : d114477 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7651, d114477, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18380 q ha hb
    | true =>
      simp only [d7651, d114477, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18364 q ha hb
  have h2 (q : Pattern) (ha : d85512 q = 1) (hb : d112688 q = 1) : d114478 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d85512, d114478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d85512, d114478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d7656 q = 1) (hb : d112688 q = 1) : d114480 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7656, d114480, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18381 q ha hb
    | true =>
      simp only [d7656, d114480, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d7657 q = 1) (hb : d112688 q = 1) : d114481 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d7657, d114481, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d7657, d114481, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d85513 q = 1) (hb : d112688 q = 1) : d114482 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d85513, d114482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d85513, d114482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d85521 q = 1) (hb : d112688 q = 1) : d114492 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d85521, d114492, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d85521, d114492, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d85522 q = 1) (hb : d112688 q = 1) : d114493 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d85522, d114493, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d85522, d114493, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d85523 q = 1) (hb : d112688 q = 1) : d114494 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d85523, d114494, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d85523, d114494, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro18384 (p : Pattern) (ha : d970 p = 1) (hb : d94753 p = 1) : d12854 p = 1 := by
  have h0 (q : Pattern) (ha : d1 q = 1) (hb : d969 q = 1) : d969 q = 1 := by
    exact hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d663 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d970 q = 1) (hb : d94753 q = 1) : d12854 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d970, d94753, d12854, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d970, d94753, d12854, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  exact h2 p ha hb
theorem andIntro18385 (p : Pattern) (ha : d7677 p = 1) (hb : d112688 p = 1) : d114505 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d94753 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d977 q = 1) (hb : d94753 q = 1) : d12855 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d977, d12855, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18384 q ha hb
    | true =>
      simp only [d977, d12855, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12527 q ha hb
  have h2 (q : Pattern) (ha : d978 q = 1) (hb : d94753 q = 1) : d12856 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d978, d12856, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d978, d12856, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d979 q = 1) (hb : d94753 q = 1) : d12857 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d979, d12857, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d979, d12857, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d112686 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d981 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d982 q = 1) (hb : d112686 q = 1) : d114500 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d982, d112686, d114500, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12527 q ha hb
    | true =>
      simp only [d982, d112686, d114500, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d983 q = 1) (hb : d112686 q = 1) : d114501 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d983, d114501, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d983, d114501, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d984 q = 1) (hb : d112686 q = 1) : d114502 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d984, d114502, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d984, d114502, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d985 q = 1) (hb : d112687 q = 1) : d114503 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d985, d112687, d114503, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d985, d112687, d114503, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d7676 q = 1) (hb : d112688 q = 1) : d114504 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d7676, d112688, d114504, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d7676, d112688, d114504, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d112688 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d7677 q = 1) (hb : d112688 q = 1) : d114505 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d7677, d114505, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d7677, d114505, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  exact h13 p ha hb
theorem andIntro18386 (p : Pattern) (ha : d7681 p = 1) (hb : d112688 p = 1) : d114510 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d94753 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d982 q = 1) (hb : d94753 q = 1) : d12868 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d982, d12868, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12527 q ha hb
    | true =>
      simp only [d982, d12868, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12524 q ha hb
  have h2 (q : Pattern) (ha : d983 q = 1) (hb : d94753 q = 1) : d12869 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d983, d12869, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d983, d12869, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d984 q = 1) (hb : d94753 q = 1) : d12870 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d984, d12870, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d984, d12870, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d112686 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d986 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d987 q = 1) (hb : d112686 q = 1) : d88553 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d987, d112686, d88553, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12524 q ha hb
    | true =>
      simp only [d987, d112686, d88553, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d988 q = 1) (hb : d112686 q = 1) : d88554 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d988, d88554, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d988, d88554, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d989 q = 1) (hb : d112686 q = 1) : d88555 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d989, d88555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d989, d88555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d990 q = 1) (hb : d112687 q = 1) : d114508 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d990, d112687, d114508, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d990, d112687, d114508, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d7680 q = 1) (hb : d112688 q = 1) : d114509 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d7680, d112688, d114509, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d7680, d112688, d114509, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d112688 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d7681 q = 1) (hb : d112688 q = 1) : d114510 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d7681, d114510, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d7681, d114510, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  exact h13 p ha hb
theorem andIntro18387 (p : Pattern) (ha : d7687 p = 1) (hb : d112688 p = 1) : d114516 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d112688 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d7678 q = 1) (hb : d112688 q = 1) : d114506 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d7678, d114506, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18385 q ha hb
    | true =>
      simp only [d7678, d114506, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d7679 q = 1) (hb : d112688 q = 1) : d114507 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d7679, d114507, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7679, d114507, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d7682 q = 1) (hb : d112688 q = 1) : d114511 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d7682, d114511, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18386 q ha hb
    | true =>
      simp only [d7682, d114511, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d7683 q = 1) (hb : d112688 q = 1) : d114512 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d7683, d114512, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7683, d114512, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d7684 q = 1) (hb : d112688 q = 1) : d114513 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d7684, d114513, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d7684, d114513, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d7685 q = 1) (hb : d112688 q = 1) : d114514 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d7685, d114514, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d7685, d114514, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d7686 q = 1) (hb : d112688 q = 1) : d114515 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d7686, d114515, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d7686, d114515, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d7687 q = 1) (hb : d112688 q = 1) : d114516 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d7687, d114516, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d7687, d114516, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro18388 (p : Pattern) (ha : d7691 p = 1) (hb : d112688 p = 1) : d114520 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d112688 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d7682 q = 1) (hb : d112688 q = 1) : d114511 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d7682, d114511, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18386 q ha hb
    | true =>
      simp only [d7682, d114511, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d7683 q = 1) (hb : d112688 q = 1) : d114512 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d7683, d114512, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7683, d114512, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d1006 q = 1) (hb : d112688 q = 1) : d12886 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d1006, d12886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18358 q ha hb
    | true =>
      simp only [d1006, d12886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d1007 q = 1) (hb : d112688 q = 1) : d12887 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d1007, d12887, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1007, d12887, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d7688 q = 1) (hb : d112688 q = 1) : d114517 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d7688, d114517, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d7688, d114517, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d7689 q = 1) (hb : d112688 q = 1) : d114518 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d7689, d114518, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d7689, d114518, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d7690 q = 1) (hb : d112688 q = 1) : d114519 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d7690, d114519, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d7690, d114519, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d7691 q = 1) (hb : d112688 q = 1) : d114520 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d7691, d114520, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d7691, d114520, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro18389 (p : Pattern) (ha : d7706 p = 1) (hb : d112688 p = 1) : d114526 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d112688 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d7682 q = 1) (hb : d112688 q = 1) : d114511 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d7682, d114511, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18386 q ha hb
    | true =>
      simp only [d7682, d114511, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d7683 q = 1) (hb : d112688 q = 1) : d114512 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d7683, d114512, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7683, d114512, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d7703 q = 1) (hb : d112688 q = 1) : d114523 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d7703, d114523, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d7703, d114523, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d7704 q = 1) (hb : d112688 q = 1) : d114524 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d7704, d114524, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d7704, d114524, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d7705 q = 1) (hb : d112688 q = 1) : d114525 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d7705, d114525, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d7705, d114525, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d7706 q = 1) (hb : d112688 q = 1) : d114526 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d7706, d114526, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d7706, d114526, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro18390 (p : Pattern) (ha : d85533 p = 1) (hb : d112688 p = 1) : d114532 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d112688 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d7692 q = 1) (hb : d112688 q = 1) : d114521 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7692, d114521, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18387 q ha hb
    | true =>
      simp only [d7692, d114521, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18388 q ha hb
  have h2 (q : Pattern) (ha : d85529 q = 1) (hb : d112688 q = 1) : d114522 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d85529, d114522, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d85529, d114522, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d7707 q = 1) (hb : d112688 q = 1) : d114527 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7707, d114527, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18389 q ha hb
    | true =>
      simp only [d7707, d114527, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d7708 q = 1) (hb : d112688 q = 1) : d114528 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d7708, d114528, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d7708, d114528, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d85530 q = 1) (hb : d112688 q = 1) : d114529 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d85530, d114529, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d85530, d114529, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d85531 q = 1) (hb : d112688 q = 1) : d114530 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d85531, d114530, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d85531, d114530, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d85532 q = 1) (hb : d112688 q = 1) : d114531 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d85532, d114531, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d85532, d114531, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d85533 q = 1) (hb : d112688 q = 1) : d114532 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d85533, d114532, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d85533, d114532, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro18391 (p : Pattern) (ha : d85539 p = 1) (hb : d112688 p = 1) : d114538 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d112688 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d7588 q = 1) (hb : d112688 q = 1) : d114419 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d7588, d114419, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7588, d114419, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18363 q ha hb
  have h2 (q : Pattern) (ha : d7589 q = 1) (hb : d112688 q = 1) : d114420 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d7589, d114420, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d7589, d114420, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d7597 q = 1) (hb : d112688 q = 1) : d114428 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d7597, d114428, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18363 q ha hb
    | true =>
      simp only [d7597, d114428, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18365 q ha hb
  have h4 (q : Pattern) (ha : d7598 q = 1) (hb : d112688 q = 1) : d114429 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d7598, d114429, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d7598, d114429, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d7599 q = 1) (hb : d112688 q = 1) : d114430 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d7599, d114430, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d7599, d114430, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d85517 q = 1) (hb : d112688 q = 1) : d114486 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d85517, d114486, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18375 q ha hb
    | true =>
      simp only [d85517, d114486, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18382 q ha hb
  have h7 (q : Pattern) (ha : d7664 q = 1) (hb : d112688 q = 1) : d114488 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d7664, d114488, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18366 q ha hb
    | true =>
      simp only [d7664, d114488, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18356 q ha hb
  have h8 (q : Pattern) (ha : d85518 q = 1) (hb : d112688 q = 1) : d114489 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d85518, d114489, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d85518, d114489, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d85519 q = 1) (hb : d112688 q = 1) : d114490 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d85519, d114490, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d85519, d114490, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d85520 q = 1) (hb : d112688 q = 1) : d114491 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d85520, d114491, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d85520, d114491, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d85524 q = 1) (hb : d112688 q = 1) : d114495 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d85524, d114495, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d85524, d114495, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18383 q ha hb
  have h12 (q : Pattern) (ha : d960 q = 1) (hb : d112688 q = 1) : d12849 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d960, d12849, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d960, d12849, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18357 q ha hb
  have h13 (q : Pattern) (ha : d85525 q = 1) (hb : d112688 q = 1) : d114496 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d85525, d114496, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d85525, d114496, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d85526 q = 1) (hb : d112688 q = 1) : d114497 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d85526, d114497, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d85526, d114497, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d85527 q = 1) (hb : d112688 q = 1) : d114498 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d85527, d114498, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d85527, d114498, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h16 (q : Pattern) (ha : d85528 q = 1) (hb : d112688 q = 1) : d114499 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d85528, d114499, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d85528, d114499, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d85534 q = 1) (hb : d112688 q = 1) : d114533 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d85534, d114533, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d85534, d114533, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18390 q ha hb
  have h18 (q : Pattern) (ha : d1070 q = 1) (hb : d112688 q = 1) : d12942 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d1070, d12942, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1070, d12942, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18360 q ha hb
  have h19 (q : Pattern) (ha : d85535 q = 1) (hb : d112688 q = 1) : d114534 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d85535, d114534, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d85535, d114534, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d85536 q = 1) (hb : d112688 q = 1) : d114535 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d85536, d114535, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d85536, d114535, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h21 (q : Pattern) (ha : d85537 q = 1) (hb : d112688 q = 1) : d114536 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d85537, d114536, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d85537, d114536, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h22 (q : Pattern) (ha : d85538 q = 1) (hb : d112688 q = 1) : d114537 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d85538, d114537, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d85538, d114537, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h23 (q : Pattern) (ha : d85539 q = 1) (hb : d112688 q = 1) : d114538 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d85539, d114538, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d85539, d114538, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
  exact h23 p ha hb
theorem andIntro18392 (p : Pattern) (ha : d85545 p = 1) (hb : d112688 p = 1) : d114544 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d112688 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d85540 q = 1) (hb : d112688 q = 1) : d114539 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d85540, d114539, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d85540, d114539, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18391 q ha hb
  have h2 (q : Pattern) (ha : d85541 q = 1) (hb : d112688 q = 1) : d114540 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d85541, d114540, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d85541, d114540, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d85542 q = 1) (hb : d112688 q = 1) : d114541 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d85542, d114541, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d85542, d114541, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d85543 q = 1) (hb : d112688 q = 1) : d114542 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d85543, d114542, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d85543, d114542, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d85544 q = 1) (hb : d112688 q = 1) : d114543 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d85544, d114543, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d85544, d114543, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d85545 q = 1) (hb : d112688 q = 1) : d114544 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d85545, d114544, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d85545, d114544, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro18393 (p : Pattern) (ha : d1152 p = 1) (hb : d112688 p = 1) : d12971 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d94753 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1142 q = 1) (hb : d94753 q = 1) : d12962 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d1142, d12962, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12536 q ha hb
    | true =>
      simp only [d1142, d12962, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12537 q ha hb
  have h2 (q : Pattern) (ha : d1143 q = 1) (hb : d94753 q = 1) : d12963 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d1143, d12963, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1143, d12963, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d1144 q = 1) (hb : d94753 q = 1) : d12964 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d1144, d12964, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1144, d12964, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d112686 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d1146 q = 1) (hb : d112687 q = 1) : d12965 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d1146, d112687, d12965, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d1146, d112687, d12965, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d1151 q = 1) (hb : d112688 q = 1) : d12970 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d1151, d112688, d12970, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d1151, d112688, d12970, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d112688 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d1152 q = 1) (hb : d112688 q = 1) : d12971 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d1152, d12971, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d1152, d12971, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro18394 (p : Pattern) (ha : d1162 p = 1) (hb : d112688 p = 1) : d12981 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d112688 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1153 q = 1) (hb : d112688 q = 1) : d12972 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d1153, d12972, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18393 q ha hb
    | true =>
      simp only [d1153, d12972, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d1154 q = 1) (hb : d112688 q = 1) : d12973 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d1154, d12973, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1154, d12973, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d1159 q = 1) (hb : d112688 q = 1) : d12978 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d1159, d12978, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d1159, d12978, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d1160 q = 1) (hb : d112688 q = 1) : d12979 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d1160, d12979, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d1160, d12979, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d1161 q = 1) (hb : d112688 q = 1) : d12980 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d1161, d12980, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d1161, d12980, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d1162 q = 1) (hb : d112688 q = 1) : d12981 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d1162, d12981, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1162, d12981, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro18395 (p : Pattern) (ha : d1172 p = 1) (hb : d112688 p = 1) : d12991 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d112688 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1153 q = 1) (hb : d112688 q = 1) : d12972 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d1153, d12972, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18393 q ha hb
    | true =>
      simp only [d1153, d12972, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d1154 q = 1) (hb : d112688 q = 1) : d12973 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d1154, d12973, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1154, d12973, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d1159 q = 1) (hb : d112688 q = 1) : d12978 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d1159, d12978, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d1159, d12978, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d1160 q = 1) (hb : d112688 q = 1) : d12979 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d1160, d12979, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d1160, d12979, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d1161 q = 1) (hb : d112688 q = 1) : d12980 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d1161, d12980, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d1161, d12980, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d1172 q = 1) (hb : d112688 q = 1) : d12991 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d1172, d12991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d1172, d12991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro18396 (p : Pattern) (ha : d1361 p = 1) (hb : d112688 p = 1) : d13140 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d112688 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1350 q = 1) (hb : d112688 q = 1) : d13129 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d1350, d13129, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18394 q ha hb
    | true =>
      simp only [d1350, d13129, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d1351 q = 1) (hb : d112688 q = 1) : d13130 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d1351, d13130, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1351, d13130, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d1352 q = 1) (hb : d112688 q = 1) : d13131 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d1352, d13131, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d1352, d13131, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d1353 q = 1) (hb : d112688 q = 1) : d13132 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d1353, d13132, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1353, d13132, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d1354 q = 1) (hb : d112688 q = 1) : d13133 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d1354, d13133, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1354, d13133, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d1356 q = 1) (hb : d112688 q = 1) : d13135 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d1356, d13135, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18395 q ha hb
    | true =>
      simp only [d1356, d13135, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d1357 q = 1) (hb : d112688 q = 1) : d13136 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d1357, d13136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1357, d13136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d1358 q = 1) (hb : d112688 q = 1) : d13137 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d1358, d13137, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d1358, d13137, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d1359 q = 1) (hb : d112688 q = 1) : d13138 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d1359, d13138, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1359, d13138, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d1360 q = 1) (hb : d112688 q = 1) : d13139 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d1360, d13139, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1360, d13139, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d1361 q = 1) (hb : d112688 q = 1) : d13140 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d1361, d13140, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d1361, d13140, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro18397 (p : Pattern) (ha : d1370 p = 1) (hb : d112688 p = 1) : d13149 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d112688 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1356 q = 1) (hb : d112688 q = 1) : d13135 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d1356, d13135, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18395 q ha hb
    | true =>
      simp only [d1356, d13135, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d1357 q = 1) (hb : d112688 q = 1) : d13136 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d1357, d13136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1357, d13136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d1358 q = 1) (hb : d112688 q = 1) : d13137 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d1358, d13137, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d1358, d13137, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d1359 q = 1) (hb : d112688 q = 1) : d13138 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d1359, d13138, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1359, d13138, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d1360 q = 1) (hb : d112688 q = 1) : d13139 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d1360, d13139, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1360, d13139, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d1370 q = 1) (hb : d112688 q = 1) : d13149 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d1370, d13149, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1370, d13149, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro18398 (p : Pattern) (ha : d1430 p = 1) (hb : d112688 p = 1) : d13196 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d94753 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1412 q = 1) (hb : d94753 q = 1) : d13191 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d1412, d13191, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12573 q ha hb
    | true =>
      simp only [d1412, d13191, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12574 q ha hb
  have h2 (q : Pattern) (ha : d1413 q = 1) (hb : d94753 q = 1) : d13192 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d1413, d13192, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1413, d13192, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d1414 q = 1) (hb : d94753 q = 1) : d13193 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d1414, d13193, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1414, d13193, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d112686 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d1420 q = 1) (hb : d112687 q = 1) : d13194 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d1420, d112687, d13194, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d1420, d112687, d13194, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d1429 q = 1) (hb : d112688 q = 1) : d13195 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d1429, d112688, d13195, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d1429, d112688, d13195, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d112688 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d1430 q = 1) (hb : d112688 q = 1) : d13196 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d1430, d13196, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d1430, d13196, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro18399 (p : Pattern) (ha : d1497 p = 1) (hb : d112688 p = 1) : d13260 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d112688 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1431 q = 1) (hb : d112688 q = 1) : d13197 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d1431, d13197, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18398 q ha hb
    | true =>
      simp only [d1431, d13197, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d1432 q = 1) (hb : d112688 q = 1) : d13198 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d1432, d13198, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1432, d13198, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d1494 q = 1) (hb : d112688 q = 1) : d13257 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d1494, d13257, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d1494, d13257, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d1495 q = 1) (hb : d112688 q = 1) : d13258 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d1495, d13258, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d1495, d13258, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d1496 q = 1) (hb : d112688 q = 1) : d13259 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d1496, d13259, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d1496, d13259, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d1497 q = 1) (hb : d112688 q = 1) : d13260 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d1497, d13260, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d1497, d13260, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro18400 (p : Pattern) (ha : d1503 p = 1) (hb : d112688 p = 1) : d13266 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d112688 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1498 q = 1) (hb : d112688 q = 1) : d13261 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d1498, d13261, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18399 q ha hb
    | true =>
      simp only [d1498, d13261, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d1499 q = 1) (hb : d112688 q = 1) : d13262 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d1499, d13262, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1499, d13262, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d1500 q = 1) (hb : d112688 q = 1) : d13263 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d1500, d13263, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d1500, d13263, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d1501 q = 1) (hb : d112688 q = 1) : d13264 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d1501, d13264, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1501, d13264, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d1502 q = 1) (hb : d112688 q = 1) : d13265 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d1502, d13265, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1502, d13265, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d1503 q = 1) (hb : d112688 q = 1) : d13266 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d1503, d13266, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1503, d13266, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro18401 (p : Pattern) (ha : d7728 p = 1) (hb : d112688 p = 1) : d114549 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d94753 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1129 q = 1) (hb : d94753 q = 1) : d12957 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d1129, d12957, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12559 q ha hb
    | true =>
      simp only [d1129, d12957, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12536 q ha hb
  have h2 (q : Pattern) (ha : d1130 q = 1) (hb : d94753 q = 1) : d12958 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d1130, d12958, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1130, d12958, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d1131 q = 1) (hb : d94753 q = 1) : d12959 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d1131, d12959, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1131, d12959, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d112686 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d1141 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d1142 q = 1) (hb : d112686 q = 1) : d88641 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d1142, d112686, d88641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12536 q ha hb
    | true =>
      simp only [d1142, d112686, d88641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d1143 q = 1) (hb : d112686 q = 1) : d88642 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d1143, d88642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d1143, d88642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d1144 q = 1) (hb : d112686 q = 1) : d88643 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d1144, d88643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d1144, d88643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d1145 q = 1) (hb : d112687 q = 1) : d114547 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d1145, d112687, d114547, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d1145, d112687, d114547, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d7727 q = 1) (hb : d112688 q = 1) : d114548 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d7727, d112688, d114548, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d7727, d112688, d114548, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d112688 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d7728 q = 1) (hb : d112688 q = 1) : d114549 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d7728, d114549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d7728, d114549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  exact h13 p ha hb
theorem andIntro18402 (p : Pattern) (ha : d7734 p = 1) (hb : d112688 p = 1) : d114555 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d112688 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d7729 q = 1) (hb : d112688 q = 1) : d114550 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d7729, d114550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18401 q ha hb
    | true =>
      simp only [d7729, d114550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d7730 q = 1) (hb : d112688 q = 1) : d114551 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d7730, d114551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7730, d114551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d1153 q = 1) (hb : d112688 q = 1) : d12972 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d1153, d12972, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18393 q ha hb
    | true =>
      simp only [d1153, d12972, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d1154 q = 1) (hb : d112688 q = 1) : d12973 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d1154, d12973, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1154, d12973, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d7731 q = 1) (hb : d112688 q = 1) : d114552 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d7731, d114552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d7731, d114552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d7732 q = 1) (hb : d112688 q = 1) : d114553 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d7732, d114553, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d7732, d114553, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d7733 q = 1) (hb : d112688 q = 1) : d114554 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d7733, d114554, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d7733, d114554, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d7734 q = 1) (hb : d112688 q = 1) : d114555 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d7734, d114555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7734, d114555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro18403 (p : Pattern) (ha : d7740 p = 1) (hb : d112688 p = 1) : d114561 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d112688 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d7735 q = 1) (hb : d112688 q = 1) : d114556 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7735, d114556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18402 q ha hb
    | true =>
      simp only [d7735, d114556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18394 q ha hb
  have h2 (q : Pattern) (ha : d7736 q = 1) (hb : d112688 q = 1) : d114557 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d7736, d114557, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7736, d114557, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d7737 q = 1) (hb : d112688 q = 1) : d114558 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d7737, d114558, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d7737, d114558, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d7738 q = 1) (hb : d112688 q = 1) : d114559 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d7738, d114559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7738, d114559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d7739 q = 1) (hb : d112688 q = 1) : d114560 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d7739, d114560, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7739, d114560, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d7740 q = 1) (hb : d112688 q = 1) : d114561 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d7740, d114561, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7740, d114561, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro18404 (p : Pattern) (ha : d7743 p = 1) (hb : d112688 p = 1) : d114564 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d112688 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d7729 q = 1) (hb : d112688 q = 1) : d114550 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d7729, d114550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18401 q ha hb
    | true =>
      simp only [d7729, d114550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d7730 q = 1) (hb : d112688 q = 1) : d114551 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d7730, d114551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7730, d114551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d1153 q = 1) (hb : d112688 q = 1) : d12972 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d1153, d12972, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18393 q ha hb
    | true =>
      simp only [d1153, d12972, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d1154 q = 1) (hb : d112688 q = 1) : d12973 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d1154, d12973, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1154, d12973, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d7731 q = 1) (hb : d112688 q = 1) : d114552 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d7731, d114552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d7731, d114552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d7732 q = 1) (hb : d112688 q = 1) : d114553 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d7732, d114553, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d7732, d114553, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d7733 q = 1) (hb : d112688 q = 1) : d114554 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d7733, d114554, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d7733, d114554, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d7743 q = 1) (hb : d112688 q = 1) : d114564 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d7743, d114564, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d7743, d114564, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro18405 (p : Pattern) (ha : d7749 p = 1) (hb : d112688 p = 1) : d114570 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d112688 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d7735 q = 1) (hb : d112688 q = 1) : d114556 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7735, d114556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18402 q ha hb
    | true =>
      simp only [d7735, d114556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18394 q ha hb
  have h2 (q : Pattern) (ha : d7736 q = 1) (hb : d112688 q = 1) : d114557 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d7736, d114557, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7736, d114557, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d7737 q = 1) (hb : d112688 q = 1) : d114558 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d7737, d114558, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d7737, d114558, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d7738 q = 1) (hb : d112688 q = 1) : d114559 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d7738, d114559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7738, d114559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d7739 q = 1) (hb : d112688 q = 1) : d114560 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d7739, d114560, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7739, d114560, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d7744 q = 1) (hb : d112688 q = 1) : d114565 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7744, d114565, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18404 q ha hb
    | true =>
      simp only [d7744, d114565, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18395 q ha hb
  have h7 (q : Pattern) (ha : d7745 q = 1) (hb : d112688 q = 1) : d114566 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d7745, d114566, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7745, d114566, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d7746 q = 1) (hb : d112688 q = 1) : d114567 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d7746, d114567, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d7746, d114567, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d7747 q = 1) (hb : d112688 q = 1) : d114568 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d7747, d114568, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7747, d114568, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d7748 q = 1) (hb : d112688 q = 1) : d114569 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d7748, d114569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7748, d114569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d7749 q = 1) (hb : d112688 q = 1) : d114570 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d7749, d114570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d7749, d114570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro18406 (p : Pattern) (ha : d7816 p = 1) (hb : d112688 p = 1) : d114630 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d112688 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d7735 q = 1) (hb : d112688 q = 1) : d114556 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7735, d114556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18402 q ha hb
    | true =>
      simp only [d7735, d114556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18394 q ha hb
  have h2 (q : Pattern) (ha : d7736 q = 1) (hb : d112688 q = 1) : d114557 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d7736, d114557, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7736, d114557, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d7737 q = 1) (hb : d112688 q = 1) : d114558 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d7737, d114558, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d7737, d114558, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d7738 q = 1) (hb : d112688 q = 1) : d114559 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d7738, d114559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7738, d114559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d7739 q = 1) (hb : d112688 q = 1) : d114560 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d7739, d114560, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7739, d114560, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d1350 q = 1) (hb : d112688 q = 1) : d13129 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d1350, d13129, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18394 q ha hb
    | true =>
      simp only [d1350, d13129, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d1351 q = 1) (hb : d112688 q = 1) : d13130 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d1351, d13130, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1351, d13130, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d1352 q = 1) (hb : d112688 q = 1) : d13131 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d1352, d13131, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d1352, d13131, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d1353 q = 1) (hb : d112688 q = 1) : d13132 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d1353, d13132, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1353, d13132, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d1354 q = 1) (hb : d112688 q = 1) : d13133 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d1354, d13133, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1354, d13133, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d7816 q = 1) (hb : d112688 q = 1) : d114630 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d7816, d114630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d7816, d114630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro18407 (p : Pattern) (ha : d1185 p = 1) (hb : d112688 p = 1) : d13004 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d112688 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1153 q = 1) (hb : d112688 q = 1) : d12972 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d1153, d12972, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18393 q ha hb
    | true =>
      simp only [d1153, d12972, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d1154 q = 1) (hb : d112688 q = 1) : d12973 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d1154, d12973, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1154, d12973, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d1159 q = 1) (hb : d112688 q = 1) : d12978 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d1159, d12978, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d1159, d12978, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d1160 q = 1) (hb : d112688 q = 1) : d12979 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d1160, d12979, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d1160, d12979, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d1184 q = 1) (hb : d112688 q = 1) : d13003 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d1184, d13003, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1184, d13003, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d1185 q = 1) (hb : d112688 q = 1) : d13004 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d1185, d13004, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1185, d13004, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro18408 (p : Pattern) (ha : d1195 p = 1) (hb : d112688 p = 1) : d13014 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d112688 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1153 q = 1) (hb : d112688 q = 1) : d12972 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d1153, d12972, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18393 q ha hb
    | true =>
      simp only [d1153, d12972, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d1154 q = 1) (hb : d112688 q = 1) : d12973 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d1154, d12973, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1154, d12973, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d1159 q = 1) (hb : d112688 q = 1) : d12978 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d1159, d12978, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d1159, d12978, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d1193 q = 1) (hb : d112688 q = 1) : d13012 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d1193, d13012, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1193, d13012, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d1194 q = 1) (hb : d112688 q = 1) : d13013 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d1194, d13013, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d1194, d13013, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d1195 q = 1) (hb : d112688 q = 1) : d13014 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d1195, d13014, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1195, d13014, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro18409 (p : Pattern) (ha : d7754 p = 1) (hb : d112688 p = 1) : d114575 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d112688 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d7729 q = 1) (hb : d112688 q = 1) : d114550 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d7729, d114550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18401 q ha hb
    | true =>
      simp only [d7729, d114550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d7730 q = 1) (hb : d112688 q = 1) : d114551 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d7730, d114551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7730, d114551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d1153 q = 1) (hb : d112688 q = 1) : d12972 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d1153, d12972, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18393 q ha hb
    | true =>
      simp only [d1153, d12972, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d1154 q = 1) (hb : d112688 q = 1) : d12973 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d1154, d12973, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1154, d12973, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d7731 q = 1) (hb : d112688 q = 1) : d114552 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d7731, d114552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d7731, d114552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d7732 q = 1) (hb : d112688 q = 1) : d114553 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d7732, d114553, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d7732, d114553, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d7753 q = 1) (hb : d112688 q = 1) : d114574 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d7753, d114574, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7753, d114574, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d7754 q = 1) (hb : d112688 q = 1) : d114575 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d7754, d114575, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7754, d114575, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro18410 (p : Pattern) (ha : d7761 p = 1) (hb : d112688 p = 1) : d114582 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d112688 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d7729 q = 1) (hb : d112688 q = 1) : d114550 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d7729, d114550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18401 q ha hb
    | true =>
      simp only [d7729, d114550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d7730 q = 1) (hb : d112688 q = 1) : d114551 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d7730, d114551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7730, d114551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d1153 q = 1) (hb : d112688 q = 1) : d12972 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d1153, d12972, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18393 q ha hb
    | true =>
      simp only [d1153, d12972, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d1154 q = 1) (hb : d112688 q = 1) : d12973 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d1154, d12973, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1154, d12973, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d7731 q = 1) (hb : d112688 q = 1) : d114552 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d7731, d114552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d7731, d114552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d7759 q = 1) (hb : d112688 q = 1) : d114580 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d7759, d114580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7759, d114580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d7760 q = 1) (hb : d112688 q = 1) : d114581 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d7760, d114581, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d7760, d114581, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d7761 q = 1) (hb : d112688 q = 1) : d114582 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d7761, d114582, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7761, d114582, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro18411 (p : Pattern) (ha : d1215 p = 1) (hb : d94753 p = 1) : d13018 p = 1 := by
  have h0 (q : Pattern) (ha : d1 q = 1) (hb : d1214 q = 1) : d1214 q = 1 := by
    exact hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1114 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d1215 q = 1) (hb : d94753 q = 1) : d13018 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d1215, d94753, d13018, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d1215, d94753, d13018, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  exact h2 p ha hb
theorem andIntro18412 (p : Pattern) (ha : d7766 p = 1) (hb : d112688 p = 1) : d114591 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d94753 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1216 q = 1) (hb : d94753 q = 1) : d13019 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d1216, d13019, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18411 q ha hb
    | true =>
      simp only [d1216, d13019, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12559 q ha hb
  have h2 (q : Pattern) (ha : d1217 q = 1) (hb : d94753 q = 1) : d13020 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d1217, d13020, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1217, d13020, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d1218 q = 1) (hb : d94753 q = 1) : d13021 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d1218, d13021, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1218, d13021, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d112686 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d1128 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d1129 q = 1) (hb : d112686 q = 1) : d114586 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d1129, d112686, d114586, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12559 q ha hb
    | true =>
      simp only [d1129, d112686, d114586, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d1130 q = 1) (hb : d112686 q = 1) : d114587 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d1130, d114587, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d1130, d114587, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d1131 q = 1) (hb : d112686 q = 1) : d114588 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d1131, d114588, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d1131, d114588, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d1219 q = 1) (hb : d112687 q = 1) : d114589 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d1219, d112687, d114589, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d1219, d112687, d114589, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d7765 q = 1) (hb : d112688 q = 1) : d114590 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d7765, d112688, d114590, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d7765, d112688, d114590, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d112688 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d7766 q = 1) (hb : d112688 q = 1) : d114591 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d7766, d114591, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d7766, d114591, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  exact h13 p ha hb
theorem andIntro18413 (p : Pattern) (ha : d7772 p = 1) (hb : d112688 p = 1) : d114597 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d112688 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d7767 q = 1) (hb : d112688 q = 1) : d114592 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d7767, d114592, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18412 q ha hb
    | true =>
      simp only [d7767, d114592, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d7768 q = 1) (hb : d112688 q = 1) : d114593 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d7768, d114593, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7768, d114593, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d7729 q = 1) (hb : d112688 q = 1) : d114550 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d7729, d114550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18401 q ha hb
    | true =>
      simp only [d7729, d114550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d7730 q = 1) (hb : d112688 q = 1) : d114551 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d7730, d114551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7730, d114551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d7769 q = 1) (hb : d112688 q = 1) : d114594 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d7769, d114594, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d7769, d114594, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d7770 q = 1) (hb : d112688 q = 1) : d114595 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d7770, d114595, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d7770, d114595, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d7771 q = 1) (hb : d112688 q = 1) : d114596 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d7771, d114596, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d7771, d114596, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d7772 q = 1) (hb : d112688 q = 1) : d114597 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d7772, d114597, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7772, d114597, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro18414 (p : Pattern) (ha : d7787 p = 1) (hb : d112688 p = 1) : d114603 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d112688 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d7729 q = 1) (hb : d112688 q = 1) : d114550 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d7729, d114550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18401 q ha hb
    | true =>
      simp only [d7729, d114550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d7730 q = 1) (hb : d112688 q = 1) : d114551 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d7730, d114551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7730, d114551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d7784 q = 1) (hb : d112688 q = 1) : d114600 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d7784, d114600, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d7784, d114600, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d7785 q = 1) (hb : d112688 q = 1) : d114601 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d7785, d114601, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d7785, d114601, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d7786 q = 1) (hb : d112688 q = 1) : d114602 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d7786, d114602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d7786, d114602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d7787 q = 1) (hb : d112688 q = 1) : d114603 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d7787, d114603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7787, d114603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro18415 (p : Pattern) (ha : d85552 p = 1) (hb : d112688 p = 1) : d114609 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d112688 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d7755 q = 1) (hb : d112688 q = 1) : d114576 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7755, d114576, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18409 q ha hb
    | true =>
      simp only [d7755, d114576, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18407 q ha hb
  have h2 (q : Pattern) (ha : d7756 q = 1) (hb : d112688 q = 1) : d114577 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d7756, d114577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7756, d114577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d7757 q = 1) (hb : d112688 q = 1) : d114578 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d7757, d114578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d7757, d114578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d7758 q = 1) (hb : d112688 q = 1) : d114579 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d7758, d114579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7758, d114579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d7762 q = 1) (hb : d112688 q = 1) : d114583 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7762, d114583, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18410 q ha hb
    | true =>
      simp only [d7762, d114583, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18408 q ha hb
  have h6 (q : Pattern) (ha : d7763 q = 1) (hb : d112688 q = 1) : d114584 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d7763, d114584, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7763, d114584, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d7764 q = 1) (hb : d112688 q = 1) : d114585 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d7764, d114585, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d7764, d114585, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d7773 q = 1) (hb : d112688 q = 1) : d114598 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7773, d114598, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18413 q ha hb
    | true =>
      simp only [d7773, d114598, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18402 q ha hb
  have h9 (q : Pattern) (ha : d85548 q = 1) (hb : d112688 q = 1) : d114599 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d85548, d114599, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d85548, d114599, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d7788 q = 1) (hb : d112688 q = 1) : d114604 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7788, d114604, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18414 q ha hb
    | true =>
      simp only [d7788, d114604, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d7789 q = 1) (hb : d112688 q = 1) : d114605 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d7789, d114605, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d7789, d114605, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d85549 q = 1) (hb : d112688 q = 1) : d114606 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d85549, d114606, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d85549, d114606, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d85550 q = 1) (hb : d112688 q = 1) : d114607 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d85550, d114607, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d85550, d114607, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d85551 q = 1) (hb : d112688 q = 1) : d114608 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d85551, d114608, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d85551, d114608, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d85552 q = 1) (hb : d112688 q = 1) : d114609 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d85552, d114609, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d85552, d114609, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro18416 (p : Pattern) (ha : d1327 p = 1) (hb : d112688 p = 1) : d13099 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d112688 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1153 q = 1) (hb : d112688 q = 1) : d12972 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d1153, d12972, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18393 q ha hb
    | true =>
      simp only [d1153, d12972, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d1154 q = 1) (hb : d112688 q = 1) : d12973 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d1154, d12973, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1154, d12973, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d1159 q = 1) (hb : d112688 q = 1) : d12978 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d1159, d12978, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d1159, d12978, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d1160 q = 1) (hb : d112688 q = 1) : d12979 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d1160, d12979, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d1160, d12979, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d1184 q = 1) (hb : d112688 q = 1) : d13003 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d1184, d13003, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1184, d13003, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d1327 q = 1) (hb : d112688 q = 1) : d13099 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d1327, d13099, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d1327, d13099, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro18417 (p : Pattern) (ha : d1333 p = 1) (hb : d112688 p = 1) : d13105 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d112688 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1153 q = 1) (hb : d112688 q = 1) : d12972 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d1153, d12972, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18393 q ha hb
    | true =>
      simp only [d1153, d12972, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d1154 q = 1) (hb : d112688 q = 1) : d12973 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d1154, d12973, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1154, d12973, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d1159 q = 1) (hb : d112688 q = 1) : d12978 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d1159, d12978, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d1159, d12978, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d1193 q = 1) (hb : d112688 q = 1) : d13012 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d1193, d13012, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1193, d13012, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d1194 q = 1) (hb : d112688 q = 1) : d13013 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d1194, d13013, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d1194, d13013, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d1333 q = 1) (hb : d112688 q = 1) : d13105 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d1333, d13105, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d1333, d13105, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro18418 (p : Pattern) (ha : d7794 p = 1) (hb : d112688 p = 1) : d114610 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d112688 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d7729 q = 1) (hb : d112688 q = 1) : d114550 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d7729, d114550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18401 q ha hb
    | true =>
      simp only [d7729, d114550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d7730 q = 1) (hb : d112688 q = 1) : d114551 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d7730, d114551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7730, d114551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d1153 q = 1) (hb : d112688 q = 1) : d12972 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d1153, d12972, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18393 q ha hb
    | true =>
      simp only [d1153, d12972, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d1154 q = 1) (hb : d112688 q = 1) : d12973 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d1154, d12973, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1154, d12973, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d7731 q = 1) (hb : d112688 q = 1) : d114552 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d7731, d114552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d7731, d114552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d7732 q = 1) (hb : d112688 q = 1) : d114553 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d7732, d114553, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d7732, d114553, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d7753 q = 1) (hb : d112688 q = 1) : d114574 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d7753, d114574, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7753, d114574, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d7794 q = 1) (hb : d112688 q = 1) : d114610 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d7794, d114610, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d7794, d114610, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro18419 (p : Pattern) (ha : d7799 p = 1) (hb : d112688 p = 1) : d114615 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d112688 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d7729 q = 1) (hb : d112688 q = 1) : d114550 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d7729, d114550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18401 q ha hb
    | true =>
      simp only [d7729, d114550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d7730 q = 1) (hb : d112688 q = 1) : d114551 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d7730, d114551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7730, d114551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d1153 q = 1) (hb : d112688 q = 1) : d12972 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d1153, d12972, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18393 q ha hb
    | true =>
      simp only [d1153, d12972, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d1154 q = 1) (hb : d112688 q = 1) : d12973 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d1154, d12973, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1154, d12973, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d7731 q = 1) (hb : d112688 q = 1) : d114552 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d7731, d114552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d7731, d114552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d7759 q = 1) (hb : d112688 q = 1) : d114580 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d7759, d114580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7759, d114580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d7760 q = 1) (hb : d112688 q = 1) : d114581 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d7760, d114581, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d7760, d114581, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d7799 q = 1) (hb : d112688 q = 1) : d114615 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d7799, d114615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d7799, d114615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro18420 (p : Pattern) (ha : d7803 p = 1) (hb : d112688 p = 1) : d114619 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d112688 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d7767 q = 1) (hb : d112688 q = 1) : d114592 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d7767, d114592, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18412 q ha hb
    | true =>
      simp only [d7767, d114592, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d7768 q = 1) (hb : d112688 q = 1) : d114593 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d7768, d114593, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7768, d114593, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d7729 q = 1) (hb : d112688 q = 1) : d114550 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d7729, d114550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18401 q ha hb
    | true =>
      simp only [d7729, d114550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d7730 q = 1) (hb : d112688 q = 1) : d114551 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d7730, d114551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7730, d114551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d7769 q = 1) (hb : d112688 q = 1) : d114594 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d7769, d114594, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d7769, d114594, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d7770 q = 1) (hb : d112688 q = 1) : d114595 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d7770, d114595, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d7770, d114595, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d7771 q = 1) (hb : d112688 q = 1) : d114596 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d7771, d114596, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d7771, d114596, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d7803 q = 1) (hb : d112688 q = 1) : d114619 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d7803, d114619, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d7803, d114619, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro18421 (p : Pattern) (ha : d7808 p = 1) (hb : d112688 p = 1) : d114622 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d112688 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d7729 q = 1) (hb : d112688 q = 1) : d114550 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d7729, d114550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18401 q ha hb
    | true =>
      simp only [d7729, d114550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d7730 q = 1) (hb : d112688 q = 1) : d114551 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d7730, d114551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7730, d114551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d7784 q = 1) (hb : d112688 q = 1) : d114600 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d7784, d114600, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d7784, d114600, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d7785 q = 1) (hb : d112688 q = 1) : d114601 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d7785, d114601, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d7785, d114601, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d7786 q = 1) (hb : d112688 q = 1) : d114602 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d7786, d114602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d7786, d114602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d7808 q = 1) (hb : d112688 q = 1) : d114622 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d7808, d114622, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d7808, d114622, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro18422 (p : Pattern) (ha : d85557 p = 1) (hb : d112688 p = 1) : d114628 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d112688 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d7755 q = 1) (hb : d112688 q = 1) : d114576 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7755, d114576, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18409 q ha hb
    | true =>
      simp only [d7755, d114576, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18407 q ha hb
  have h2 (q : Pattern) (ha : d7756 q = 1) (hb : d112688 q = 1) : d114577 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d7756, d114577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7756, d114577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d7757 q = 1) (hb : d112688 q = 1) : d114578 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d7757, d114578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d7757, d114578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d7758 q = 1) (hb : d112688 q = 1) : d114579 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d7758, d114579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7758, d114579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d7762 q = 1) (hb : d112688 q = 1) : d114583 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7762, d114583, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18410 q ha hb
    | true =>
      simp only [d7762, d114583, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18408 q ha hb
  have h6 (q : Pattern) (ha : d7763 q = 1) (hb : d112688 q = 1) : d114584 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d7763, d114584, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7763, d114584, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d7764 q = 1) (hb : d112688 q = 1) : d114585 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d7764, d114585, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d7764, d114585, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d7773 q = 1) (hb : d112688 q = 1) : d114598 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7773, d114598, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18413 q ha hb
    | true =>
      simp only [d7773, d114598, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18402 q ha hb
  have h9 (q : Pattern) (ha : d85548 q = 1) (hb : d112688 q = 1) : d114599 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d85548, d114599, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d85548, d114599, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d7788 q = 1) (hb : d112688 q = 1) : d114604 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7788, d114604, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18414 q ha hb
    | true =>
      simp only [d7788, d114604, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d7789 q = 1) (hb : d112688 q = 1) : d114605 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d7789, d114605, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d7789, d114605, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d85549 q = 1) (hb : d112688 q = 1) : d114606 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d85549, d114606, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d85549, d114606, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d85550 q = 1) (hb : d112688 q = 1) : d114607 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d85550, d114607, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d85550, d114607, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d85551 q = 1) (hb : d112688 q = 1) : d114608 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d85551, d114608, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d85551, d114608, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d7795 q = 1) (hb : d112688 q = 1) : d114611 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7795, d114611, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18418 q ha hb
    | true =>
      simp only [d7795, d114611, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18416 q ha hb
  have h16 (q : Pattern) (ha : d7796 q = 1) (hb : d112688 q = 1) : d114612 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d7796, d114612, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7796, d114612, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d7797 q = 1) (hb : d112688 q = 1) : d114613 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d7797, d114613, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d7797, d114613, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h18 (q : Pattern) (ha : d7798 q = 1) (hb : d112688 q = 1) : d114614 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d7798, d114614, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7798, d114614, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d7800 q = 1) (hb : d112688 q = 1) : d114616 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7800, d114616, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18419 q ha hb
    | true =>
      simp only [d7800, d114616, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18417 q ha hb
  have h20 (q : Pattern) (ha : d7801 q = 1) (hb : d112688 q = 1) : d114617 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d7801, d114617, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7801, d114617, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
  have h21 (q : Pattern) (ha : d7802 q = 1) (hb : d112688 q = 1) : d114618 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d7802, d114618, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d7802, d114618, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h22 (q : Pattern) (ha : d7804 q = 1) (hb : d112688 q = 1) : d114620 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7804, d114620, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18420 q ha hb
    | true =>
      simp only [d7804, d114620, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18404 q ha hb
  have h23 (q : Pattern) (ha : d85553 q = 1) (hb : d112688 q = 1) : d114621 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d85553, d114621, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
    | true =>
      simp only [d85553, d114621, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h24 (q : Pattern) (ha : d7809 q = 1) (hb : d112688 q = 1) : d114623 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7809, d114623, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18421 q ha hb
    | true =>
      simp only [d7809, d114623, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h25 (q : Pattern) (ha : d7810 q = 1) (hb : d112688 q = 1) : d114624 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d7810, d114624, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q ha hb
    | true =>
      simp only [d7810, d114624, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h26 (q : Pattern) (ha : d85554 q = 1) (hb : d112688 q = 1) : d114625 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d85554, d114625, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
    | true =>
      simp only [d85554, d114625, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q ha hb
  have h27 (q : Pattern) (ha : d85555 q = 1) (hb : d112688 q = 1) : d114626 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d85555, d114626, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d85555, d114626, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h26 q ha hb
  have h28 (q : Pattern) (ha : d85556 q = 1) (hb : d112688 q = 1) : d114627 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d85556, d114627, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d85556, d114627, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h27 q ha hb
  have h29 (q : Pattern) (ha : d85557 q = 1) (hb : d112688 q = 1) : d114628 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d85557, d114628, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d85557, d114628, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h28 q ha hb
  exact h29 p ha hb
theorem andIntro18423 (p : Pattern) (ha : d85564 p = 1) (hb : d112688 p = 1) : d114637 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d112688 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d7804 q = 1) (hb : d112688 q = 1) : d114620 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7804, d114620, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18420 q ha hb
    | true =>
      simp only [d7804, d114620, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18404 q ha hb
  have h2 (q : Pattern) (ha : d85553 q = 1) (hb : d112688 q = 1) : d114621 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d85553, d114621, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d85553, d114621, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d7809 q = 1) (hb : d112688 q = 1) : d114623 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7809, d114623, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18421 q ha hb
    | true =>
      simp only [d7809, d114623, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d7810 q = 1) (hb : d112688 q = 1) : d114624 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d7810, d114624, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d7810, d114624, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d85554 q = 1) (hb : d112688 q = 1) : d114625 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d85554, d114625, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d85554, d114625, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d85562 q = 1) (hb : d112688 q = 1) : d114635 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d85562, d114635, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d85562, d114635, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d85563 q = 1) (hb : d112688 q = 1) : d114636 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d85563, d114636, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d85563, d114636, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d85564 q = 1) (hb : d112688 q = 1) : d114637 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d85564, d114637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d85564, d114637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro18424 (p : Pattern) (ha : d1390 p = 1) (hb : d94753 p = 1) : d13155 p = 1 := by
  have h0 (q : Pattern) (ha : d1 q = 1) (hb : d1384 q = 1) : d1384 q = 1 := by
    exact hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1389 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d1390 q = 1) (hb : d94753 q = 1) : d13155 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d1390, d94753, d13155, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d1390, d94753, d13155, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  exact h2 p ha hb
theorem andIntro18425 (p : Pattern) (ha : d7830 p = 1) (hb : d112688 p = 1) : d114648 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d94753 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1397 q = 1) (hb : d94753 q = 1) : d13157 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d1397, d13157, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18424 q ha hb
    | true =>
      simp only [d1397, d13157, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12577 q ha hb
  have h2 (q : Pattern) (ha : d1398 q = 1) (hb : d94753 q = 1) : d13158 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d1398, d13158, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1398, d13158, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d1399 q = 1) (hb : d94753 q = 1) : d13159 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d1399, d13159, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1399, d13159, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d112686 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d1401 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d1402 q = 1) (hb : d112686 q = 1) : d114643 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d1402, d112686, d114643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12577 q ha hb
    | true =>
      simp only [d1402, d112686, d114643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d1403 q = 1) (hb : d112686 q = 1) : d114644 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d1403, d114644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d1403, d114644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d1404 q = 1) (hb : d112686 q = 1) : d114645 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d1404, d114645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d1404, d114645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d1405 q = 1) (hb : d112687 q = 1) : d114646 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d1405, d112687, d114646, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d1405, d112687, d114646, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d7829 q = 1) (hb : d112688 q = 1) : d114647 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d7829, d112688, d114647, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d7829, d112688, d114647, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d112688 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d7830 q = 1) (hb : d112688 q = 1) : d114648 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d7830, d114648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d7830, d114648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  exact h13 p ha hb
theorem andIntro18426 (p : Pattern) (ha : d7834 p = 1) (hb : d112688 p = 1) : d114653 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d94753 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1402 q = 1) (hb : d94753 q = 1) : d13174 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d1402, d13174, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12577 q ha hb
    | true =>
      simp only [d1402, d13174, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12573 q ha hb
  have h2 (q : Pattern) (ha : d1403 q = 1) (hb : d94753 q = 1) : d13175 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d1403, d13175, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1403, d13175, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d1404 q = 1) (hb : d94753 q = 1) : d13176 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d1404, d13176, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1404, d13176, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d112686 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d1411 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d1412 q = 1) (hb : d112686 q = 1) : d88705 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d1412, d112686, d88705, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12573 q ha hb
    | true =>
      simp only [d1412, d112686, d88705, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d1413 q = 1) (hb : d112686 q = 1) : d88706 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d1413, d88706, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d1413, d88706, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d1414 q = 1) (hb : d112686 q = 1) : d88707 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d1414, d88707, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d1414, d88707, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d1415 q = 1) (hb : d112687 q = 1) : d114651 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d1415, d112687, d114651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d1415, d112687, d114651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d7833 q = 1) (hb : d112688 q = 1) : d114652 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d7833, d112688, d114652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d7833, d112688, d114652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d112688 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d7834 q = 1) (hb : d112688 q = 1) : d114653 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d7834, d114653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d7834, d114653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  exact h13 p ha hb
theorem andIntro18427 (p : Pattern) (ha : d7840 p = 1) (hb : d112688 p = 1) : d114659 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d112688 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d7831 q = 1) (hb : d112688 q = 1) : d114649 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d7831, d114649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18425 q ha hb
    | true =>
      simp only [d7831, d114649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d7832 q = 1) (hb : d112688 q = 1) : d114650 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d7832, d114650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7832, d114650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d7835 q = 1) (hb : d112688 q = 1) : d114654 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d7835, d114654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18426 q ha hb
    | true =>
      simp only [d7835, d114654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d7836 q = 1) (hb : d112688 q = 1) : d114655 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d7836, d114655, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7836, d114655, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d7837 q = 1) (hb : d112688 q = 1) : d114656 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d7837, d114656, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d7837, d114656, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d7838 q = 1) (hb : d112688 q = 1) : d114657 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d7838, d114657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d7838, d114657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d7839 q = 1) (hb : d112688 q = 1) : d114658 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d7839, d114658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d7839, d114658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d7840 q = 1) (hb : d112688 q = 1) : d114659 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d7840, d114659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d7840, d114659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro18428 (p : Pattern) (ha : d7844 p = 1) (hb : d112688 p = 1) : d114663 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d112688 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d7835 q = 1) (hb : d112688 q = 1) : d114654 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d7835, d114654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18426 q ha hb
    | true =>
      simp only [d7835, d114654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d7836 q = 1) (hb : d112688 q = 1) : d114655 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d7836, d114655, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7836, d114655, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d1431 q = 1) (hb : d112688 q = 1) : d13197 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d1431, d13197, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18398 q ha hb
    | true =>
      simp only [d1431, d13197, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d1432 q = 1) (hb : d112688 q = 1) : d13198 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d1432, d13198, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1432, d13198, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d7841 q = 1) (hb : d112688 q = 1) : d114660 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d7841, d114660, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d7841, d114660, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d7842 q = 1) (hb : d112688 q = 1) : d114661 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d7842, d114661, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d7842, d114661, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d7843 q = 1) (hb : d112688 q = 1) : d114662 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d7843, d114662, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d7843, d114662, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d7844 q = 1) (hb : d112688 q = 1) : d114663 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d7844, d114663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d7844, d114663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro18429 (p : Pattern) (ha : d7859 p = 1) (hb : d112688 p = 1) : d114669 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d112688 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d7835 q = 1) (hb : d112688 q = 1) : d114654 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d7835, d114654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18426 q ha hb
    | true =>
      simp only [d7835, d114654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d7836 q = 1) (hb : d112688 q = 1) : d114655 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d7836, d114655, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7836, d114655, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d7856 q = 1) (hb : d112688 q = 1) : d114666 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d7856, d114666, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d7856, d114666, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d7857 q = 1) (hb : d112688 q = 1) : d114667 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d7857, d114667, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d7857, d114667, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d7858 q = 1) (hb : d112688 q = 1) : d114668 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d7858, d114668, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d7858, d114668, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d7859 q = 1) (hb : d112688 q = 1) : d114669 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d7859, d114669, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d7859, d114669, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro18430 (p : Pattern) (ha : d85574 p = 1) (hb : d112688 p = 1) : d114675 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d112688 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d7845 q = 1) (hb : d112688 q = 1) : d114664 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7845, d114664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18427 q ha hb
    | true =>
      simp only [d7845, d114664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18428 q ha hb
  have h2 (q : Pattern) (ha : d85570 q = 1) (hb : d112688 q = 1) : d114665 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d85570, d114665, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d85570, d114665, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d7860 q = 1) (hb : d112688 q = 1) : d114670 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7860, d114670, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18429 q ha hb
    | true =>
      simp only [d7860, d114670, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d7861 q = 1) (hb : d112688 q = 1) : d114671 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d7861, d114671, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d7861, d114671, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d85571 q = 1) (hb : d112688 q = 1) : d114672 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d85571, d114672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d85571, d114672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d85572 q = 1) (hb : d112688 q = 1) : d114673 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d85572, d114673, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d85572, d114673, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d85573 q = 1) (hb : d112688 q = 1) : d114674 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d85573, d114674, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d85573, d114674, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d85574 q = 1) (hb : d112688 q = 1) : d114675 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d85574, d114675, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d85574, d114675, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro18431 (p : Pattern) (ha : d85580 p = 1) (hb : d112688 p = 1) : d114681 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d112688 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d7741 q = 1) (hb : d112688 q = 1) : d114562 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d7741, d114562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7741, d114562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18403 q ha hb
  have h2 (q : Pattern) (ha : d7742 q = 1) (hb : d112688 q = 1) : d114563 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d7742, d114563, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d7742, d114563, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d7750 q = 1) (hb : d112688 q = 1) : d114571 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d7750, d114571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18403 q ha hb
    | true =>
      simp only [d7750, d114571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18405 q ha hb
  have h4 (q : Pattern) (ha : d7751 q = 1) (hb : d112688 q = 1) : d114572 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d7751, d114572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d7751, d114572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d7752 q = 1) (hb : d112688 q = 1) : d114573 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d7752, d114573, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d7752, d114573, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d85558 q = 1) (hb : d112688 q = 1) : d114629 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d85558, d114629, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18415 q ha hb
    | true =>
      simp only [d85558, d114629, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18422 q ha hb
  have h7 (q : Pattern) (ha : d7817 q = 1) (hb : d112688 q = 1) : d114631 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d7817, d114631, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18406 q ha hb
    | true =>
      simp only [d7817, d114631, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18396 q ha hb
  have h8 (q : Pattern) (ha : d85559 q = 1) (hb : d112688 q = 1) : d114632 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d85559, d114632, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d85559, d114632, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d85560 q = 1) (hb : d112688 q = 1) : d114633 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d85560, d114633, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d85560, d114633, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d85561 q = 1) (hb : d112688 q = 1) : d114634 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d85561, d114634, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d85561, d114634, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d85565 q = 1) (hb : d112688 q = 1) : d114638 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d85565, d114638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d85565, d114638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18423 q ha hb
  have h12 (q : Pattern) (ha : d1371 q = 1) (hb : d112688 q = 1) : d13150 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d1371, d13150, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1371, d13150, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18397 q ha hb
  have h13 (q : Pattern) (ha : d85566 q = 1) (hb : d112688 q = 1) : d114639 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d85566, d114639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d85566, d114639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d85567 q = 1) (hb : d112688 q = 1) : d114640 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d85567, d114640, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d85567, d114640, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d85568 q = 1) (hb : d112688 q = 1) : d114641 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d85568, d114641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d85568, d114641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h16 (q : Pattern) (ha : d85569 q = 1) (hb : d112688 q = 1) : d114642 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d85569, d114642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d85569, d114642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d85575 q = 1) (hb : d112688 q = 1) : d114676 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d85575, d114676, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d85575, d114676, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18430 q ha hb
  have h18 (q : Pattern) (ha : d1504 q = 1) (hb : d112688 q = 1) : d13267 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d1504, d13267, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1504, d13267, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18400 q ha hb
  have h19 (q : Pattern) (ha : d85576 q = 1) (hb : d112688 q = 1) : d114677 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d85576, d114677, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d85576, d114677, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d85577 q = 1) (hb : d112688 q = 1) : d114678 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d85577, d114678, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d85577, d114678, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h21 (q : Pattern) (ha : d85578 q = 1) (hb : d112688 q = 1) : d114679 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d85578, d114679, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d85578, d114679, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h22 (q : Pattern) (ha : d85579 q = 1) (hb : d112688 q = 1) : d114680 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d85579, d114680, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d85579, d114680, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h23 (q : Pattern) (ha : d85580 q = 1) (hb : d112688 q = 1) : d114681 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d85580, d114681, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d85580, d114681, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
  exact h23 p ha hb
theorem andIntro18432 (p : Pattern) (ha : d85586 p = 1) (hb : d112688 p = 1) : d114687 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d112688 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d85581 q = 1) (hb : d112688 q = 1) : d114682 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d85581, d114682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d85581, d114682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18431 q ha hb
  have h2 (q : Pattern) (ha : d85582 q = 1) (hb : d112688 q = 1) : d114683 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d85582, d114683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d85582, d114683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d85583 q = 1) (hb : d112688 q = 1) : d114684 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d85583, d114684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d85583, d114684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d85584 q = 1) (hb : d112688 q = 1) : d114685 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d85584, d114685, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d85584, d114685, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d85585 q = 1) (hb : d112688 q = 1) : d114686 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d85585, d114686, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d85585, d114686, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d85586 q = 1) (hb : d112688 q = 1) : d114687 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d85586, d114687, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d85586, d114687, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro18433 (p : Pattern) (ha : d1613 p = 1) (hb : d112688 p = 1) : d13297 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d94753 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1603 q = 1) (hb : d94753 q = 1) : d13288 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d1603, d13288, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12586 q ha hb
    | true =>
      simp only [d1603, d13288, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12587 q ha hb
  have h2 (q : Pattern) (ha : d1604 q = 1) (hb : d94753 q = 1) : d13289 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d1604, d13289, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1604, d13289, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d1605 q = 1) (hb : d94753 q = 1) : d13290 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d1605, d13290, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1605, d13290, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d112686 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d1607 q = 1) (hb : d112687 q = 1) : d13291 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d1607, d112687, d13291, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d1607, d112687, d13291, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d1612 q = 1) (hb : d112688 q = 1) : d13296 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d1612, d112688, d13296, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d1612, d112688, d13296, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d112688 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d1613 q = 1) (hb : d112688 q = 1) : d13297 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d1613, d13297, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d1613, d13297, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro18434 (p : Pattern) (ha : d1623 p = 1) (hb : d112688 p = 1) : d13307 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d112688 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1614 q = 1) (hb : d112688 q = 1) : d13298 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d1614, d13298, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18433 q ha hb
    | true =>
      simp only [d1614, d13298, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d1615 q = 1) (hb : d112688 q = 1) : d13299 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d1615, d13299, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1615, d13299, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d1620 q = 1) (hb : d112688 q = 1) : d13304 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d1620, d13304, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d1620, d13304, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d1621 q = 1) (hb : d112688 q = 1) : d13305 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d1621, d13305, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d1621, d13305, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d1622 q = 1) (hb : d112688 q = 1) : d13306 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d1622, d13306, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d1622, d13306, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d1623 q = 1) (hb : d112688 q = 1) : d13307 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d1623, d13307, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1623, d13307, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro18435 (p : Pattern) (ha : d1633 p = 1) (hb : d112688 p = 1) : d13317 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d112688 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1614 q = 1) (hb : d112688 q = 1) : d13298 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d1614, d13298, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18433 q ha hb
    | true =>
      simp only [d1614, d13298, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d1615 q = 1) (hb : d112688 q = 1) : d13299 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d1615, d13299, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1615, d13299, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d1620 q = 1) (hb : d112688 q = 1) : d13304 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d1620, d13304, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d1620, d13304, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d1621 q = 1) (hb : d112688 q = 1) : d13305 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d1621, d13305, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d1621, d13305, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d1622 q = 1) (hb : d112688 q = 1) : d13306 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d1622, d13306, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d1622, d13306, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d1633 q = 1) (hb : d112688 q = 1) : d13317 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d1633, d13317, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d1633, d13317, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro18436 (p : Pattern) (ha : d1838 p = 1) (hb : d112688 p = 1) : d13466 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d112688 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1827 q = 1) (hb : d112688 q = 1) : d13455 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d1827, d13455, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18434 q ha hb
    | true =>
      simp only [d1827, d13455, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d1828 q = 1) (hb : d112688 q = 1) : d13456 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d1828, d13456, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1828, d13456, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d1829 q = 1) (hb : d112688 q = 1) : d13457 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d1829, d13457, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d1829, d13457, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d1830 q = 1) (hb : d112688 q = 1) : d13458 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d1830, d13458, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1830, d13458, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d1831 q = 1) (hb : d112688 q = 1) : d13459 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d1831, d13459, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1831, d13459, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d1833 q = 1) (hb : d112688 q = 1) : d13461 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d1833, d13461, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18435 q ha hb
    | true =>
      simp only [d1833, d13461, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d1834 q = 1) (hb : d112688 q = 1) : d13462 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d1834, d13462, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1834, d13462, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d1835 q = 1) (hb : d112688 q = 1) : d13463 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d1835, d13463, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d1835, d13463, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d1836 q = 1) (hb : d112688 q = 1) : d13464 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d1836, d13464, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1836, d13464, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d1837 q = 1) (hb : d112688 q = 1) : d13465 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d1837, d13465, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1837, d13465, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d1838 q = 1) (hb : d112688 q = 1) : d13466 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d1838, d13466, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d1838, d13466, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro18437 (p : Pattern) (ha : d1847 p = 1) (hb : d112688 p = 1) : d13475 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d112688 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1833 q = 1) (hb : d112688 q = 1) : d13461 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d1833, d13461, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18435 q ha hb
    | true =>
      simp only [d1833, d13461, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d1834 q = 1) (hb : d112688 q = 1) : d13462 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d1834, d13462, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1834, d13462, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d1835 q = 1) (hb : d112688 q = 1) : d13463 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d1835, d13463, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d1835, d13463, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d1836 q = 1) (hb : d112688 q = 1) : d13464 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d1836, d13464, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1836, d13464, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d1837 q = 1) (hb : d112688 q = 1) : d13465 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d1837, d13465, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1837, d13465, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d1847 q = 1) (hb : d112688 q = 1) : d13475 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d1847, d13475, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1847, d13475, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro18438 (p : Pattern) (ha : d1907 p = 1) (hb : d112688 p = 1) : d13522 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d94753 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1889 q = 1) (hb : d94753 q = 1) : d13517 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d1889, d13517, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12623 q ha hb
    | true =>
      simp only [d1889, d13517, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12624 q ha hb
  have h2 (q : Pattern) (ha : d1890 q = 1) (hb : d94753 q = 1) : d13518 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d1890, d13518, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1890, d13518, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d1891 q = 1) (hb : d94753 q = 1) : d13519 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d1891, d13519, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1891, d13519, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d112686 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d1897 q = 1) (hb : d112687 q = 1) : d13520 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d1897, d112687, d13520, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d1897, d112687, d13520, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d1906 q = 1) (hb : d112688 q = 1) : d13521 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d1906, d112688, d13521, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d1906, d112688, d13521, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d112688 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d1907 q = 1) (hb : d112688 q = 1) : d13522 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d1907, d13522, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d1907, d13522, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro18439 (p : Pattern) (ha : d1974 p = 1) (hb : d112688 p = 1) : d13586 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d112688 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1908 q = 1) (hb : d112688 q = 1) : d13523 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d1908, d13523, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18438 q ha hb
    | true =>
      simp only [d1908, d13523, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d1909 q = 1) (hb : d112688 q = 1) : d13524 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d1909, d13524, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1909, d13524, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d1971 q = 1) (hb : d112688 q = 1) : d13583 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d1971, d13583, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d1971, d13583, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d1972 q = 1) (hb : d112688 q = 1) : d13584 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d1972, d13584, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d1972, d13584, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d1973 q = 1) (hb : d112688 q = 1) : d13585 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d1973, d13585, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d1973, d13585, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d1974 q = 1) (hb : d112688 q = 1) : d13586 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d1974, d13586, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d1974, d13586, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro18440 (p : Pattern) (ha : d1980 p = 1) (hb : d112688 p = 1) : d13592 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d112688 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1975 q = 1) (hb : d112688 q = 1) : d13587 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d1975, d13587, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18439 q ha hb
    | true =>
      simp only [d1975, d13587, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d1976 q = 1) (hb : d112688 q = 1) : d13588 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d1976, d13588, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1976, d13588, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d1977 q = 1) (hb : d112688 q = 1) : d13589 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d1977, d13589, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d1977, d13589, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d1978 q = 1) (hb : d112688 q = 1) : d13590 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d1978, d13590, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1978, d13590, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d1979 q = 1) (hb : d112688 q = 1) : d13591 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d1979, d13591, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1979, d13591, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d1980 q = 1) (hb : d112688 q = 1) : d13592 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d1980, d13592, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1980, d13592, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro18441 (p : Pattern) (ha : d7882 p = 1) (hb : d112688 p = 1) : d114693 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d94753 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1590 q = 1) (hb : d94753 q = 1) : d13283 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d1590, d13283, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12609 q ha hb
    | true =>
      simp only [d1590, d13283, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12586 q ha hb
  have h2 (q : Pattern) (ha : d1591 q = 1) (hb : d94753 q = 1) : d13284 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d1591, d13284, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1591, d13284, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d1592 q = 1) (hb : d94753 q = 1) : d13285 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d1592, d13285, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1592, d13285, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d112686 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d1602 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d1603 q = 1) (hb : d112686 q = 1) : d88794 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d1603, d112686, d88794, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12586 q ha hb
    | true =>
      simp only [d1603, d112686, d88794, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d1604 q = 1) (hb : d112686 q = 1) : d88795 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d1604, d88795, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d1604, d88795, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d1605 q = 1) (hb : d112686 q = 1) : d88796 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d1605, d88796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d1605, d88796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d1606 q = 1) (hb : d112687 q = 1) : d114691 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d1606, d112687, d114691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d1606, d112687, d114691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d7881 q = 1) (hb : d112688 q = 1) : d114692 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d7881, d112688, d114692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d7881, d112688, d114692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d112688 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d7882 q = 1) (hb : d112688 q = 1) : d114693 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d7882, d114693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d7882, d114693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  exact h13 p ha hb
theorem andIntro18442 (p : Pattern) (ha : d7888 p = 1) (hb : d112688 p = 1) : d114699 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d112688 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d7883 q = 1) (hb : d112688 q = 1) : d114694 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d7883, d114694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18441 q ha hb
    | true =>
      simp only [d7883, d114694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d7884 q = 1) (hb : d112688 q = 1) : d114695 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d7884, d114695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7884, d114695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d1614 q = 1) (hb : d112688 q = 1) : d13298 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d1614, d13298, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18433 q ha hb
    | true =>
      simp only [d1614, d13298, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d1615 q = 1) (hb : d112688 q = 1) : d13299 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d1615, d13299, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1615, d13299, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d7885 q = 1) (hb : d112688 q = 1) : d114696 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d7885, d114696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d7885, d114696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d7886 q = 1) (hb : d112688 q = 1) : d114697 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d7886, d114697, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d7886, d114697, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d7887 q = 1) (hb : d112688 q = 1) : d114698 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d7887, d114698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d7887, d114698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d7888 q = 1) (hb : d112688 q = 1) : d114699 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d7888, d114699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7888, d114699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro18443 (p : Pattern) (ha : d7894 p = 1) (hb : d112688 p = 1) : d114705 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d112688 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d7889 q = 1) (hb : d112688 q = 1) : d114700 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7889, d114700, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18442 q ha hb
    | true =>
      simp only [d7889, d114700, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18434 q ha hb
  have h2 (q : Pattern) (ha : d7890 q = 1) (hb : d112688 q = 1) : d114701 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d7890, d114701, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7890, d114701, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d7891 q = 1) (hb : d112688 q = 1) : d114702 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d7891, d114702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d7891, d114702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d7892 q = 1) (hb : d112688 q = 1) : d114703 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d7892, d114703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7892, d114703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d7893 q = 1) (hb : d112688 q = 1) : d114704 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d7893, d114704, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7893, d114704, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d7894 q = 1) (hb : d112688 q = 1) : d114705 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d7894, d114705, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7894, d114705, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro18444 (p : Pattern) (ha : d7897 p = 1) (hb : d112688 p = 1) : d114708 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d112688 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d7883 q = 1) (hb : d112688 q = 1) : d114694 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d7883, d114694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18441 q ha hb
    | true =>
      simp only [d7883, d114694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d7884 q = 1) (hb : d112688 q = 1) : d114695 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d7884, d114695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7884, d114695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d1614 q = 1) (hb : d112688 q = 1) : d13298 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d1614, d13298, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18433 q ha hb
    | true =>
      simp only [d1614, d13298, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d1615 q = 1) (hb : d112688 q = 1) : d13299 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d1615, d13299, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1615, d13299, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d7885 q = 1) (hb : d112688 q = 1) : d114696 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d7885, d114696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d7885, d114696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d7886 q = 1) (hb : d112688 q = 1) : d114697 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d7886, d114697, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d7886, d114697, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d7887 q = 1) (hb : d112688 q = 1) : d114698 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d7887, d114698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d7887, d114698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d7897 q = 1) (hb : d112688 q = 1) : d114708 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d7897, d114708, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d7897, d114708, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro18445 (p : Pattern) (ha : d7903 p = 1) (hb : d112688 p = 1) : d114714 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d112688 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d7889 q = 1) (hb : d112688 q = 1) : d114700 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7889, d114700, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18442 q ha hb
    | true =>
      simp only [d7889, d114700, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18434 q ha hb
  have h2 (q : Pattern) (ha : d7890 q = 1) (hb : d112688 q = 1) : d114701 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d7890, d114701, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7890, d114701, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d7891 q = 1) (hb : d112688 q = 1) : d114702 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d7891, d114702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d7891, d114702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d7892 q = 1) (hb : d112688 q = 1) : d114703 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d7892, d114703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7892, d114703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d7893 q = 1) (hb : d112688 q = 1) : d114704 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d7893, d114704, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7893, d114704, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d7898 q = 1) (hb : d112688 q = 1) : d114709 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7898, d114709, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18444 q ha hb
    | true =>
      simp only [d7898, d114709, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18435 q ha hb
  have h7 (q : Pattern) (ha : d7899 q = 1) (hb : d112688 q = 1) : d114710 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d7899, d114710, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7899, d114710, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d7900 q = 1) (hb : d112688 q = 1) : d114711 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d7900, d114711, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d7900, d114711, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d7901 q = 1) (hb : d112688 q = 1) : d114712 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d7901, d114712, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7901, d114712, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d7902 q = 1) (hb : d112688 q = 1) : d114713 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d7902, d114713, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7902, d114713, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d7903 q = 1) (hb : d112688 q = 1) : d114714 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d7903, d114714, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d7903, d114714, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro18446 (p : Pattern) (ha : d7970 p = 1) (hb : d112688 p = 1) : d114774 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d112688 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d7889 q = 1) (hb : d112688 q = 1) : d114700 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7889, d114700, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18442 q ha hb
    | true =>
      simp only [d7889, d114700, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18434 q ha hb
  have h2 (q : Pattern) (ha : d7890 q = 1) (hb : d112688 q = 1) : d114701 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d7890, d114701, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7890, d114701, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d7891 q = 1) (hb : d112688 q = 1) : d114702 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d7891, d114702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d7891, d114702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d7892 q = 1) (hb : d112688 q = 1) : d114703 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d7892, d114703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7892, d114703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d7893 q = 1) (hb : d112688 q = 1) : d114704 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d7893, d114704, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7893, d114704, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d1827 q = 1) (hb : d112688 q = 1) : d13455 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d1827, d13455, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18434 q ha hb
    | true =>
      simp only [d1827, d13455, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d1828 q = 1) (hb : d112688 q = 1) : d13456 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d1828, d13456, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1828, d13456, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d1829 q = 1) (hb : d112688 q = 1) : d13457 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d1829, d13457, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d1829, d13457, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d1830 q = 1) (hb : d112688 q = 1) : d13458 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d1830, d13458, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1830, d13458, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d1831 q = 1) (hb : d112688 q = 1) : d13459 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d1831, d13459, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1831, d13459, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d7970 q = 1) (hb : d112688 q = 1) : d114774 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d7970, d114774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d7970, d114774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro18447 (p : Pattern) (ha : d1646 p = 1) (hb : d112688 p = 1) : d13330 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d112688 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1614 q = 1) (hb : d112688 q = 1) : d13298 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d1614, d13298, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18433 q ha hb
    | true =>
      simp only [d1614, d13298, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d1615 q = 1) (hb : d112688 q = 1) : d13299 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d1615, d13299, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1615, d13299, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d1620 q = 1) (hb : d112688 q = 1) : d13304 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d1620, d13304, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d1620, d13304, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d1621 q = 1) (hb : d112688 q = 1) : d13305 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d1621, d13305, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d1621, d13305, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d1645 q = 1) (hb : d112688 q = 1) : d13329 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d1645, d13329, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1645, d13329, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d1646 q = 1) (hb : d112688 q = 1) : d13330 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d1646, d13330, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1646, d13330, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro18448 (p : Pattern) (ha : d1656 p = 1) (hb : d112688 p = 1) : d13340 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d112688 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1614 q = 1) (hb : d112688 q = 1) : d13298 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d1614, d13298, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18433 q ha hb
    | true =>
      simp only [d1614, d13298, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d1615 q = 1) (hb : d112688 q = 1) : d13299 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d1615, d13299, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1615, d13299, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d1620 q = 1) (hb : d112688 q = 1) : d13304 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d1620, d13304, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d1620, d13304, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d1654 q = 1) (hb : d112688 q = 1) : d13338 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d1654, d13338, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1654, d13338, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d1655 q = 1) (hb : d112688 q = 1) : d13339 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d1655, d13339, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d1655, d13339, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d1656 q = 1) (hb : d112688 q = 1) : d13340 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d1656, d13340, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1656, d13340, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro18449 (p : Pattern) (ha : d7908 p = 1) (hb : d112688 p = 1) : d114719 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d112688 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d7883 q = 1) (hb : d112688 q = 1) : d114694 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d7883, d114694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18441 q ha hb
    | true =>
      simp only [d7883, d114694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d7884 q = 1) (hb : d112688 q = 1) : d114695 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d7884, d114695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7884, d114695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d1614 q = 1) (hb : d112688 q = 1) : d13298 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d1614, d13298, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18433 q ha hb
    | true =>
      simp only [d1614, d13298, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d1615 q = 1) (hb : d112688 q = 1) : d13299 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d1615, d13299, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1615, d13299, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d7885 q = 1) (hb : d112688 q = 1) : d114696 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d7885, d114696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d7885, d114696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d7886 q = 1) (hb : d112688 q = 1) : d114697 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d7886, d114697, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d7886, d114697, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d7907 q = 1) (hb : d112688 q = 1) : d114718 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d7907, d114718, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7907, d114718, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d7908 q = 1) (hb : d112688 q = 1) : d114719 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d7908, d114719, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7908, d114719, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro18450 (p : Pattern) (ha : d7915 p = 1) (hb : d112688 p = 1) : d114726 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d112688 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d7883 q = 1) (hb : d112688 q = 1) : d114694 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d7883, d114694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18441 q ha hb
    | true =>
      simp only [d7883, d114694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d7884 q = 1) (hb : d112688 q = 1) : d114695 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d7884, d114695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7884, d114695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d1614 q = 1) (hb : d112688 q = 1) : d13298 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d1614, d13298, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18433 q ha hb
    | true =>
      simp only [d1614, d13298, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d1615 q = 1) (hb : d112688 q = 1) : d13299 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d1615, d13299, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1615, d13299, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d7885 q = 1) (hb : d112688 q = 1) : d114696 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d7885, d114696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d7885, d114696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d7913 q = 1) (hb : d112688 q = 1) : d114724 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d7913, d114724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7913, d114724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d7914 q = 1) (hb : d112688 q = 1) : d114725 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d7914, d114725, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d7914, d114725, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d7915 q = 1) (hb : d112688 q = 1) : d114726 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d7915, d114726, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7915, d114726, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro18451 (p : Pattern) (ha : d1670 p = 1) (hb : d94753 p = 1) : d13344 p = 1 := by
  have h0 (q : Pattern) (ha : d1 q = 1) (hb : d1669 q = 1) : d1669 q = 1 := by
    exact hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1574 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d1670 q = 1) (hb : d94753 q = 1) : d13344 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d1670, d94753, d13344, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d1670, d94753, d13344, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  exact h2 p ha hb
theorem andIntro18452 (p : Pattern) (ha : d7920 p = 1) (hb : d112688 p = 1) : d114735 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d94753 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1671 q = 1) (hb : d94753 q = 1) : d13345 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d1671, d13345, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18451 q ha hb
    | true =>
      simp only [d1671, d13345, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12609 q ha hb
  have h2 (q : Pattern) (ha : d1672 q = 1) (hb : d94753 q = 1) : d13346 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d1672, d13346, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1672, d13346, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d1673 q = 1) (hb : d94753 q = 1) : d13347 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d1673, d13347, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1673, d13347, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d112686 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d1589 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d1590 q = 1) (hb : d112686 q = 1) : d114730 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d1590, d112686, d114730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12609 q ha hb
    | true =>
      simp only [d1590, d112686, d114730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d1591 q = 1) (hb : d112686 q = 1) : d114731 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d1591, d114731, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d1591, d114731, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d1592 q = 1) (hb : d112686 q = 1) : d114732 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d1592, d114732, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d1592, d114732, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d1674 q = 1) (hb : d112687 q = 1) : d114733 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d1674, d112687, d114733, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d1674, d112687, d114733, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d7919 q = 1) (hb : d112688 q = 1) : d114734 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d7919, d112688, d114734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d7919, d112688, d114734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d112688 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d7920 q = 1) (hb : d112688 q = 1) : d114735 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d7920, d114735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d7920, d114735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  exact h13 p ha hb
theorem andIntro18453 (p : Pattern) (ha : d7926 p = 1) (hb : d112688 p = 1) : d114741 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d112688 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d7921 q = 1) (hb : d112688 q = 1) : d114736 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d7921, d114736, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18452 q ha hb
    | true =>
      simp only [d7921, d114736, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d7922 q = 1) (hb : d112688 q = 1) : d114737 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d7922, d114737, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7922, d114737, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d7883 q = 1) (hb : d112688 q = 1) : d114694 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d7883, d114694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18441 q ha hb
    | true =>
      simp only [d7883, d114694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d7884 q = 1) (hb : d112688 q = 1) : d114695 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d7884, d114695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7884, d114695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d7923 q = 1) (hb : d112688 q = 1) : d114738 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d7923, d114738, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d7923, d114738, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d7924 q = 1) (hb : d112688 q = 1) : d114739 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d7924, d114739, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d7924, d114739, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d7925 q = 1) (hb : d112688 q = 1) : d114740 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d7925, d114740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d7925, d114740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d7926 q = 1) (hb : d112688 q = 1) : d114741 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d7926, d114741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7926, d114741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro18454 (p : Pattern) (ha : d7941 p = 1) (hb : d112688 p = 1) : d114747 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d112688 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d7883 q = 1) (hb : d112688 q = 1) : d114694 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d7883, d114694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18441 q ha hb
    | true =>
      simp only [d7883, d114694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d7884 q = 1) (hb : d112688 q = 1) : d114695 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d7884, d114695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7884, d114695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d7938 q = 1) (hb : d112688 q = 1) : d114744 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d7938, d114744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d7938, d114744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d7939 q = 1) (hb : d112688 q = 1) : d114745 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d7939, d114745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d7939, d114745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d7940 q = 1) (hb : d112688 q = 1) : d114746 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d7940, d114746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d7940, d114746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d7941 q = 1) (hb : d112688 q = 1) : d114747 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d7941, d114747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7941, d114747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro18455 (p : Pattern) (ha : d85594 p = 1) (hb : d112688 p = 1) : d114753 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d112688 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d7909 q = 1) (hb : d112688 q = 1) : d114720 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7909, d114720, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18449 q ha hb
    | true =>
      simp only [d7909, d114720, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18447 q ha hb
  have h2 (q : Pattern) (ha : d7910 q = 1) (hb : d112688 q = 1) : d114721 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d7910, d114721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7910, d114721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d7911 q = 1) (hb : d112688 q = 1) : d114722 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d7911, d114722, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d7911, d114722, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d7912 q = 1) (hb : d112688 q = 1) : d114723 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d7912, d114723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7912, d114723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d7916 q = 1) (hb : d112688 q = 1) : d114727 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7916, d114727, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18450 q ha hb
    | true =>
      simp only [d7916, d114727, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18448 q ha hb
  have h6 (q : Pattern) (ha : d7917 q = 1) (hb : d112688 q = 1) : d114728 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d7917, d114728, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7917, d114728, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d7918 q = 1) (hb : d112688 q = 1) : d114729 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d7918, d114729, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d7918, d114729, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d7927 q = 1) (hb : d112688 q = 1) : d114742 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7927, d114742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18453 q ha hb
    | true =>
      simp only [d7927, d114742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18442 q ha hb
  have h9 (q : Pattern) (ha : d85590 q = 1) (hb : d112688 q = 1) : d114743 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d85590, d114743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d85590, d114743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d7942 q = 1) (hb : d112688 q = 1) : d114748 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7942, d114748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18454 q ha hb
    | true =>
      simp only [d7942, d114748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d7943 q = 1) (hb : d112688 q = 1) : d114749 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d7943, d114749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d7943, d114749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d85591 q = 1) (hb : d112688 q = 1) : d114750 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d85591, d114750, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d85591, d114750, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d85592 q = 1) (hb : d112688 q = 1) : d114751 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d85592, d114751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d85592, d114751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d85593 q = 1) (hb : d112688 q = 1) : d114752 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d85593, d114752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d85593, d114752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d85594 q = 1) (hb : d112688 q = 1) : d114753 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d85594, d114753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d85594, d114753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro18456 (p : Pattern) (ha : d1804 p = 1) (hb : d112688 p = 1) : d13425 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d112688 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1614 q = 1) (hb : d112688 q = 1) : d13298 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d1614, d13298, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18433 q ha hb
    | true =>
      simp only [d1614, d13298, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d1615 q = 1) (hb : d112688 q = 1) : d13299 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d1615, d13299, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1615, d13299, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d1620 q = 1) (hb : d112688 q = 1) : d13304 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d1620, d13304, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d1620, d13304, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d1621 q = 1) (hb : d112688 q = 1) : d13305 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d1621, d13305, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d1621, d13305, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d1645 q = 1) (hb : d112688 q = 1) : d13329 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d1645, d13329, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1645, d13329, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d1804 q = 1) (hb : d112688 q = 1) : d13425 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d1804, d13425, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d1804, d13425, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro18457 (p : Pattern) (ha : d1810 p = 1) (hb : d112688 p = 1) : d13431 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d112688 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1614 q = 1) (hb : d112688 q = 1) : d13298 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d1614, d13298, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18433 q ha hb
    | true =>
      simp only [d1614, d13298, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d1615 q = 1) (hb : d112688 q = 1) : d13299 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d1615, d13299, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1615, d13299, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d1620 q = 1) (hb : d112688 q = 1) : d13304 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d1620, d13304, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d1620, d13304, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d1654 q = 1) (hb : d112688 q = 1) : d13338 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d1654, d13338, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1654, d13338, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d1655 q = 1) (hb : d112688 q = 1) : d13339 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d1655, d13339, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d1655, d13339, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d1810 q = 1) (hb : d112688 q = 1) : d13431 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d1810, d13431, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d1810, d13431, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro18458 (p : Pattern) (ha : d7948 p = 1) (hb : d112688 p = 1) : d114754 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d112688 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d7883 q = 1) (hb : d112688 q = 1) : d114694 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d7883, d114694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18441 q ha hb
    | true =>
      simp only [d7883, d114694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d7884 q = 1) (hb : d112688 q = 1) : d114695 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d7884, d114695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7884, d114695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d1614 q = 1) (hb : d112688 q = 1) : d13298 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d1614, d13298, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18433 q ha hb
    | true =>
      simp only [d1614, d13298, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d1615 q = 1) (hb : d112688 q = 1) : d13299 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d1615, d13299, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1615, d13299, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d7885 q = 1) (hb : d112688 q = 1) : d114696 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d7885, d114696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d7885, d114696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d7886 q = 1) (hb : d112688 q = 1) : d114697 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d7886, d114697, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d7886, d114697, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d7907 q = 1) (hb : d112688 q = 1) : d114718 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d7907, d114718, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7907, d114718, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d7948 q = 1) (hb : d112688 q = 1) : d114754 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d7948, d114754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d7948, d114754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro18459 (p : Pattern) (ha : d7953 p = 1) (hb : d112688 p = 1) : d114759 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d112688 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d7883 q = 1) (hb : d112688 q = 1) : d114694 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d7883, d114694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18441 q ha hb
    | true =>
      simp only [d7883, d114694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d7884 q = 1) (hb : d112688 q = 1) : d114695 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d7884, d114695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7884, d114695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d1614 q = 1) (hb : d112688 q = 1) : d13298 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d1614, d13298, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18433 q ha hb
    | true =>
      simp only [d1614, d13298, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d1615 q = 1) (hb : d112688 q = 1) : d13299 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d1615, d13299, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1615, d13299, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d7885 q = 1) (hb : d112688 q = 1) : d114696 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d7885, d114696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d7885, d114696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d7913 q = 1) (hb : d112688 q = 1) : d114724 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d7913, d114724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7913, d114724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d7914 q = 1) (hb : d112688 q = 1) : d114725 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d7914, d114725, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d7914, d114725, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d7953 q = 1) (hb : d112688 q = 1) : d114759 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d7953, d114759, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d7953, d114759, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro18460 (p : Pattern) (ha : d7957 p = 1) (hb : d112688 p = 1) : d114763 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d112688 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d7921 q = 1) (hb : d112688 q = 1) : d114736 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d7921, d114736, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18452 q ha hb
    | true =>
      simp only [d7921, d114736, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d7922 q = 1) (hb : d112688 q = 1) : d114737 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d7922, d114737, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7922, d114737, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d7883 q = 1) (hb : d112688 q = 1) : d114694 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d7883, d114694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18441 q ha hb
    | true =>
      simp only [d7883, d114694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d7884 q = 1) (hb : d112688 q = 1) : d114695 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d7884, d114695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7884, d114695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d7923 q = 1) (hb : d112688 q = 1) : d114738 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d7923, d114738, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d7923, d114738, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d7924 q = 1) (hb : d112688 q = 1) : d114739 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d7924, d114739, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d7924, d114739, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d7925 q = 1) (hb : d112688 q = 1) : d114740 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d7925, d114740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d7925, d114740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d7957 q = 1) (hb : d112688 q = 1) : d114763 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d7957, d114763, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d7957, d114763, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro18461 (p : Pattern) (ha : d7962 p = 1) (hb : d112688 p = 1) : d114766 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d112688 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d7883 q = 1) (hb : d112688 q = 1) : d114694 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d7883, d114694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18441 q ha hb
    | true =>
      simp only [d7883, d114694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d7884 q = 1) (hb : d112688 q = 1) : d114695 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d7884, d114695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7884, d114695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d7938 q = 1) (hb : d112688 q = 1) : d114744 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d7938, d114744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d7938, d114744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d7939 q = 1) (hb : d112688 q = 1) : d114745 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d7939, d114745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d7939, d114745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d7940 q = 1) (hb : d112688 q = 1) : d114746 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d7940, d114746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d7940, d114746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d7962 q = 1) (hb : d112688 q = 1) : d114766 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d7962, d114766, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d7962, d114766, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro18462 (p : Pattern) (ha : d85599 p = 1) (hb : d112688 p = 1) : d114772 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d112688 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d7909 q = 1) (hb : d112688 q = 1) : d114720 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7909, d114720, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18449 q ha hb
    | true =>
      simp only [d7909, d114720, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18447 q ha hb
  have h2 (q : Pattern) (ha : d7910 q = 1) (hb : d112688 q = 1) : d114721 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d7910, d114721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7910, d114721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d7911 q = 1) (hb : d112688 q = 1) : d114722 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d7911, d114722, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d7911, d114722, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d7912 q = 1) (hb : d112688 q = 1) : d114723 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d7912, d114723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7912, d114723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d7916 q = 1) (hb : d112688 q = 1) : d114727 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7916, d114727, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18450 q ha hb
    | true =>
      simp only [d7916, d114727, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18448 q ha hb
  have h6 (q : Pattern) (ha : d7917 q = 1) (hb : d112688 q = 1) : d114728 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d7917, d114728, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7917, d114728, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d7918 q = 1) (hb : d112688 q = 1) : d114729 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d7918, d114729, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d7918, d114729, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d7927 q = 1) (hb : d112688 q = 1) : d114742 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7927, d114742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18453 q ha hb
    | true =>
      simp only [d7927, d114742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18442 q ha hb
  have h9 (q : Pattern) (ha : d85590 q = 1) (hb : d112688 q = 1) : d114743 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d85590, d114743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d85590, d114743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d7942 q = 1) (hb : d112688 q = 1) : d114748 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7942, d114748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18454 q ha hb
    | true =>
      simp only [d7942, d114748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d7943 q = 1) (hb : d112688 q = 1) : d114749 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d7943, d114749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d7943, d114749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d85591 q = 1) (hb : d112688 q = 1) : d114750 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d85591, d114750, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d85591, d114750, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d85592 q = 1) (hb : d112688 q = 1) : d114751 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d85592, d114751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d85592, d114751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d85593 q = 1) (hb : d112688 q = 1) : d114752 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d85593, d114752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d85593, d114752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d7949 q = 1) (hb : d112688 q = 1) : d114755 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7949, d114755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18458 q ha hb
    | true =>
      simp only [d7949, d114755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18456 q ha hb
  have h16 (q : Pattern) (ha : d7950 q = 1) (hb : d112688 q = 1) : d114756 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d7950, d114756, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7950, d114756, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d7951 q = 1) (hb : d112688 q = 1) : d114757 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d7951, d114757, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d7951, d114757, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h18 (q : Pattern) (ha : d7952 q = 1) (hb : d112688 q = 1) : d114758 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d7952, d114758, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7952, d114758, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d7954 q = 1) (hb : d112688 q = 1) : d114760 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7954, d114760, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18459 q ha hb
    | true =>
      simp only [d7954, d114760, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18457 q ha hb
  have h20 (q : Pattern) (ha : d7955 q = 1) (hb : d112688 q = 1) : d114761 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d7955, d114761, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7955, d114761, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
  have h21 (q : Pattern) (ha : d7956 q = 1) (hb : d112688 q = 1) : d114762 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d7956, d114762, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d7956, d114762, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h22 (q : Pattern) (ha : d7958 q = 1) (hb : d112688 q = 1) : d114764 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7958, d114764, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18460 q ha hb
    | true =>
      simp only [d7958, d114764, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18444 q ha hb
  have h23 (q : Pattern) (ha : d85595 q = 1) (hb : d112688 q = 1) : d114765 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d85595, d114765, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
    | true =>
      simp only [d85595, d114765, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h24 (q : Pattern) (ha : d7963 q = 1) (hb : d112688 q = 1) : d114767 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7963, d114767, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18461 q ha hb
    | true =>
      simp only [d7963, d114767, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h25 (q : Pattern) (ha : d7964 q = 1) (hb : d112688 q = 1) : d114768 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d7964, d114768, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q ha hb
    | true =>
      simp only [d7964, d114768, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h26 (q : Pattern) (ha : d85596 q = 1) (hb : d112688 q = 1) : d114769 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d85596, d114769, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
    | true =>
      simp only [d85596, d114769, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q ha hb
  have h27 (q : Pattern) (ha : d85597 q = 1) (hb : d112688 q = 1) : d114770 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d85597, d114770, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d85597, d114770, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h26 q ha hb
  have h28 (q : Pattern) (ha : d85598 q = 1) (hb : d112688 q = 1) : d114771 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d85598, d114771, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d85598, d114771, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h27 q ha hb
  have h29 (q : Pattern) (ha : d85599 q = 1) (hb : d112688 q = 1) : d114772 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d85599, d114772, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d85599, d114772, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h28 q ha hb
  exact h29 p ha hb
theorem andIntro18463 (p : Pattern) (ha : d85606 p = 1) (hb : d112688 p = 1) : d114781 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d112688 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d7958 q = 1) (hb : d112688 q = 1) : d114764 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7958, d114764, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18460 q ha hb
    | true =>
      simp only [d7958, d114764, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18444 q ha hb
  have h2 (q : Pattern) (ha : d85595 q = 1) (hb : d112688 q = 1) : d114765 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d85595, d114765, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d85595, d114765, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d7963 q = 1) (hb : d112688 q = 1) : d114767 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7963, d114767, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18461 q ha hb
    | true =>
      simp only [d7963, d114767, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d7964 q = 1) (hb : d112688 q = 1) : d114768 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d7964, d114768, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d7964, d114768, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d85596 q = 1) (hb : d112688 q = 1) : d114769 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d85596, d114769, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d85596, d114769, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d85604 q = 1) (hb : d112688 q = 1) : d114779 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d85604, d114779, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d85604, d114779, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d85605 q = 1) (hb : d112688 q = 1) : d114780 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d85605, d114780, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d85605, d114780, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d85606 q = 1) (hb : d112688 q = 1) : d114781 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d85606, d114781, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d85606, d114781, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro18464 (p : Pattern) (ha : d1867 p = 1) (hb : d94753 p = 1) : d13481 p = 1 := by
  have h0 (q : Pattern) (ha : d1 q = 1) (hb : d1861 q = 1) : d1861 q = 1 := by
    exact hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1866 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d1867 q = 1) (hb : d94753 q = 1) : d13481 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d1867, d94753, d13481, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d1867, d94753, d13481, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  exact h2 p ha hb
theorem andIntro18465 (p : Pattern) (ha : d7984 p = 1) (hb : d112688 p = 1) : d114792 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d94753 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1874 q = 1) (hb : d94753 q = 1) : d13483 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d1874, d13483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18464 q ha hb
    | true =>
      simp only [d1874, d13483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12627 q ha hb
  have h2 (q : Pattern) (ha : d1875 q = 1) (hb : d94753 q = 1) : d13484 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d1875, d13484, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1875, d13484, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d1876 q = 1) (hb : d94753 q = 1) : d13485 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d1876, d13485, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1876, d13485, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d112686 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d1878 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d1879 q = 1) (hb : d112686 q = 1) : d114787 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d1879, d112686, d114787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12627 q ha hb
    | true =>
      simp only [d1879, d112686, d114787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d1880 q = 1) (hb : d112686 q = 1) : d114788 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d1880, d114788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d1880, d114788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d1881 q = 1) (hb : d112686 q = 1) : d114789 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d1881, d114789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d1881, d114789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d1882 q = 1) (hb : d112687 q = 1) : d114790 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d1882, d112687, d114790, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d1882, d112687, d114790, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d7983 q = 1) (hb : d112688 q = 1) : d114791 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d7983, d112688, d114791, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d7983, d112688, d114791, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d112688 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d7984 q = 1) (hb : d112688 q = 1) : d114792 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d7984, d114792, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d7984, d114792, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  exact h13 p ha hb
theorem andIntro18466 (p : Pattern) (ha : d7988 p = 1) (hb : d112688 p = 1) : d114797 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d94753 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1879 q = 1) (hb : d94753 q = 1) : d13500 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d1879, d13500, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12627 q ha hb
    | true =>
      simp only [d1879, d13500, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12623 q ha hb
  have h2 (q : Pattern) (ha : d1880 q = 1) (hb : d94753 q = 1) : d13501 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d1880, d13501, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1880, d13501, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d1881 q = 1) (hb : d94753 q = 1) : d13502 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d1881, d13502, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1881, d13502, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d112686 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d1888 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d1889 q = 1) (hb : d112686 q = 1) : d88858 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d1889, d112686, d88858, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12623 q ha hb
    | true =>
      simp only [d1889, d112686, d88858, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d1890 q = 1) (hb : d112686 q = 1) : d88859 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d1890, d88859, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d1890, d88859, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d1891 q = 1) (hb : d112686 q = 1) : d88860 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d1891, d88860, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d1891, d88860, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d1892 q = 1) (hb : d112687 q = 1) : d114795 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d1892, d112687, d114795, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d1892, d112687, d114795, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d7987 q = 1) (hb : d112688 q = 1) : d114796 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d7987, d112688, d114796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d7987, d112688, d114796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d112688 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d7988 q = 1) (hb : d112688 q = 1) : d114797 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d7988, d114797, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d7988, d114797, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  exact h13 p ha hb
theorem andIntro18467 (p : Pattern) (ha : d7994 p = 1) (hb : d112688 p = 1) : d114803 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d112688 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d7985 q = 1) (hb : d112688 q = 1) : d114793 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d7985, d114793, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18465 q ha hb
    | true =>
      simp only [d7985, d114793, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d7986 q = 1) (hb : d112688 q = 1) : d114794 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d7986, d114794, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7986, d114794, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d7989 q = 1) (hb : d112688 q = 1) : d114798 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d7989, d114798, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18466 q ha hb
    | true =>
      simp only [d7989, d114798, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d7990 q = 1) (hb : d112688 q = 1) : d114799 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d7990, d114799, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7990, d114799, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d7991 q = 1) (hb : d112688 q = 1) : d114800 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d7991, d114800, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d7991, d114800, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d7992 q = 1) (hb : d112688 q = 1) : d114801 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d7992, d114801, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d7992, d114801, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d7993 q = 1) (hb : d112688 q = 1) : d114802 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d7993, d114802, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d7993, d114802, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d7994 q = 1) (hb : d112688 q = 1) : d114803 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d7994, d114803, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d7994, d114803, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro18468 (p : Pattern) (ha : d7998 p = 1) (hb : d112688 p = 1) : d114807 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d112688 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d7989 q = 1) (hb : d112688 q = 1) : d114798 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d7989, d114798, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18466 q ha hb
    | true =>
      simp only [d7989, d114798, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d7990 q = 1) (hb : d112688 q = 1) : d114799 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d7990, d114799, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7990, d114799, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d1908 q = 1) (hb : d112688 q = 1) : d13523 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d1908, d13523, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18438 q ha hb
    | true =>
      simp only [d1908, d13523, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d1909 q = 1) (hb : d112688 q = 1) : d13524 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d1909, d13524, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1909, d13524, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d7995 q = 1) (hb : d112688 q = 1) : d114804 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d7995, d114804, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d7995, d114804, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d7996 q = 1) (hb : d112688 q = 1) : d114805 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d7996, d114805, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d7996, d114805, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d7997 q = 1) (hb : d112688 q = 1) : d114806 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d7997, d114806, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d7997, d114806, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d7998 q = 1) (hb : d112688 q = 1) : d114807 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d7998, d114807, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d7998, d114807, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro18469 (p : Pattern) (ha : d8013 p = 1) (hb : d112688 p = 1) : d114813 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d112688 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d7989 q = 1) (hb : d112688 q = 1) : d114798 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d7989, d114798, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18466 q ha hb
    | true =>
      simp only [d7989, d114798, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d7990 q = 1) (hb : d112688 q = 1) : d114799 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d7990, d114799, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7990, d114799, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d8010 q = 1) (hb : d112688 q = 1) : d114810 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d8010, d114810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d8010, d114810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d8011 q = 1) (hb : d112688 q = 1) : d114811 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d8011, d114811, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d8011, d114811, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d8012 q = 1) (hb : d112688 q = 1) : d114812 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d8012, d114812, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d8012, d114812, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d8013 q = 1) (hb : d112688 q = 1) : d114813 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d8013, d114813, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d8013, d114813, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro18470 (p : Pattern) (ha : d85616 p = 1) (hb : d112688 p = 1) : d114819 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d112688 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d7999 q = 1) (hb : d112688 q = 1) : d114808 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7999, d114808, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18467 q ha hb
    | true =>
      simp only [d7999, d114808, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18468 q ha hb
  have h2 (q : Pattern) (ha : d85612 q = 1) (hb : d112688 q = 1) : d114809 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d85612, d114809, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d85612, d114809, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d8014 q = 1) (hb : d112688 q = 1) : d114814 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d8014, d114814, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18469 q ha hb
    | true =>
      simp only [d8014, d114814, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d8015 q = 1) (hb : d112688 q = 1) : d114815 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d8015, d114815, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d8015, d114815, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d85613 q = 1) (hb : d112688 q = 1) : d114816 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d85613, d114816, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d85613, d114816, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d85614 q = 1) (hb : d112688 q = 1) : d114817 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d85614, d114817, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d85614, d114817, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d85615 q = 1) (hb : d112688 q = 1) : d114818 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d85615, d114818, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d85615, d114818, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d85616 q = 1) (hb : d112688 q = 1) : d114819 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d85616, d114819, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d85616, d114819, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro18471 (p : Pattern) (ha : d85622 p = 1) (hb : d112688 p = 1) : d114825 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d112688 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d7895 q = 1) (hb : d112688 q = 1) : d114706 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d7895, d114706, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7895, d114706, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18443 q ha hb
  have h2 (q : Pattern) (ha : d7896 q = 1) (hb : d112688 q = 1) : d114707 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d7896, d114707, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d7896, d114707, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d7904 q = 1) (hb : d112688 q = 1) : d114715 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d7904, d114715, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18443 q ha hb
    | true =>
      simp only [d7904, d114715, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18445 q ha hb
  have h4 (q : Pattern) (ha : d7905 q = 1) (hb : d112688 q = 1) : d114716 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d7905, d114716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d7905, d114716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d7906 q = 1) (hb : d112688 q = 1) : d114717 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d7906, d114717, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d7906, d114717, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d85600 q = 1) (hb : d112688 q = 1) : d114773 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d85600, d114773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18455 q ha hb
    | true =>
      simp only [d85600, d114773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18462 q ha hb
  have h7 (q : Pattern) (ha : d7971 q = 1) (hb : d112688 q = 1) : d114775 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d7971, d114775, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18446 q ha hb
    | true =>
      simp only [d7971, d114775, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18436 q ha hb
  have h8 (q : Pattern) (ha : d85601 q = 1) (hb : d112688 q = 1) : d114776 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d85601, d114776, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d85601, d114776, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d85602 q = 1) (hb : d112688 q = 1) : d114777 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d85602, d114777, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d85602, d114777, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d85603 q = 1) (hb : d112688 q = 1) : d114778 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d85603, d114778, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d85603, d114778, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d85607 q = 1) (hb : d112688 q = 1) : d114782 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d85607, d114782, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d85607, d114782, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18463 q ha hb
  have h12 (q : Pattern) (ha : d1848 q = 1) (hb : d112688 q = 1) : d13476 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d1848, d13476, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1848, d13476, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18437 q ha hb
  have h13 (q : Pattern) (ha : d85608 q = 1) (hb : d112688 q = 1) : d114783 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d85608, d114783, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d85608, d114783, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d85609 q = 1) (hb : d112688 q = 1) : d114784 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d85609, d114784, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d85609, d114784, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d85610 q = 1) (hb : d112688 q = 1) : d114785 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d85610, d114785, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d85610, d114785, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h16 (q : Pattern) (ha : d85611 q = 1) (hb : d112688 q = 1) : d114786 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d85611, d114786, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d85611, d114786, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d85617 q = 1) (hb : d112688 q = 1) : d114820 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d85617, d114820, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d85617, d114820, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18470 q ha hb
  have h18 (q : Pattern) (ha : d1981 q = 1) (hb : d112688 q = 1) : d13593 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d1981, d13593, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1981, d13593, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18440 q ha hb
  have h19 (q : Pattern) (ha : d85618 q = 1) (hb : d112688 q = 1) : d114821 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d85618, d114821, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d85618, d114821, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d85619 q = 1) (hb : d112688 q = 1) : d114822 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d85619, d114822, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d85619, d114822, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h21 (q : Pattern) (ha : d85620 q = 1) (hb : d112688 q = 1) : d114823 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d85620, d114823, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d85620, d114823, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h22 (q : Pattern) (ha : d85621 q = 1) (hb : d112688 q = 1) : d114824 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d85621, d114824, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d85621, d114824, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h23 (q : Pattern) (ha : d85622 q = 1) (hb : d112688 q = 1) : d114825 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d85622, d114825, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d85622, d114825, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
  exact h23 p ha hb
theorem andIntro18472 (p : Pattern) (ha : d85628 p = 1) (hb : d112688 p = 1) : d114831 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d112688 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d85623 q = 1) (hb : d112688 q = 1) : d114826 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d85623, d114826, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d85623, d114826, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18471 q ha hb
  have h2 (q : Pattern) (ha : d85624 q = 1) (hb : d112688 q = 1) : d114827 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d85624, d114827, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d85624, d114827, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d85625 q = 1) (hb : d112688 q = 1) : d114828 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d85625, d114828, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d85625, d114828, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d85626 q = 1) (hb : d112688 q = 1) : d114829 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d85626, d114829, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d85626, d114829, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d85627 q = 1) (hb : d112688 q = 1) : d114830 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d85627, d114830, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d85627, d114830, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d85628 q = 1) (hb : d112688 q = 1) : d114831 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d85628, d114831, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d85628, d114831, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro18473 (p : Pattern) (ha : d2096 p = 1) (hb : d112688 p = 1) : d13624 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d94753 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d2086 q = 1) (hb : d94753 q = 1) : d13615 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d2086, d13615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12636 q ha hb
    | true =>
      simp only [d2086, d13615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12637 q ha hb
  have h2 (q : Pattern) (ha : d2087 q = 1) (hb : d94753 q = 1) : d13616 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d2087, d13616, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2087, d13616, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d2088 q = 1) (hb : d94753 q = 1) : d13617 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d2088, d13617, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2088, d13617, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d112686 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d2090 q = 1) (hb : d112687 q = 1) : d13618 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d2090, d112687, d13618, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d2090, d112687, d13618, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d2095 q = 1) (hb : d112688 q = 1) : d13623 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d2095, d112688, d13623, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d2095, d112688, d13623, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d112688 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d2096 q = 1) (hb : d112688 q = 1) : d13624 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d2096, d13624, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d2096, d13624, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro18474 (p : Pattern) (ha : d2106 p = 1) (hb : d112688 p = 1) : d13634 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d112688 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d2097 q = 1) (hb : d112688 q = 1) : d13625 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d2097, d13625, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18473 q ha hb
    | true =>
      simp only [d2097, d13625, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d2098 q = 1) (hb : d112688 q = 1) : d13626 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d2098, d13626, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2098, d13626, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d2103 q = 1) (hb : d112688 q = 1) : d13631 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d2103, d13631, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d2103, d13631, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d2104 q = 1) (hb : d112688 q = 1) : d13632 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d2104, d13632, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d2104, d13632, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d2105 q = 1) (hb : d112688 q = 1) : d13633 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d2105, d13633, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d2105, d13633, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d2106 q = 1) (hb : d112688 q = 1) : d13634 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d2106, d13634, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2106, d13634, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro18475 (p : Pattern) (ha : d2116 p = 1) (hb : d112688 p = 1) : d13644 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d112688 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d2097 q = 1) (hb : d112688 q = 1) : d13625 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d2097, d13625, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18473 q ha hb
    | true =>
      simp only [d2097, d13625, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d2098 q = 1) (hb : d112688 q = 1) : d13626 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d2098, d13626, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2098, d13626, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d2103 q = 1) (hb : d112688 q = 1) : d13631 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d2103, d13631, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d2103, d13631, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d2104 q = 1) (hb : d112688 q = 1) : d13632 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d2104, d13632, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d2104, d13632, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d2105 q = 1) (hb : d112688 q = 1) : d13633 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d2105, d13633, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d2105, d13633, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d2116 q = 1) (hb : d112688 q = 1) : d13644 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d2116, d13644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d2116, d13644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro18476 (p : Pattern) (ha : d2316 p = 1) (hb : d112688 p = 1) : d13793 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d112688 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d2305 q = 1) (hb : d112688 q = 1) : d13782 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d2305, d13782, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18474 q ha hb
    | true =>
      simp only [d2305, d13782, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d2306 q = 1) (hb : d112688 q = 1) : d13783 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d2306, d13783, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2306, d13783, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d2307 q = 1) (hb : d112688 q = 1) : d13784 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d2307, d13784, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d2307, d13784, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d2308 q = 1) (hb : d112688 q = 1) : d13785 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d2308, d13785, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2308, d13785, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d2309 q = 1) (hb : d112688 q = 1) : d13786 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d2309, d13786, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2309, d13786, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d2311 q = 1) (hb : d112688 q = 1) : d13788 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d2311, d13788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18475 q ha hb
    | true =>
      simp only [d2311, d13788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d2312 q = 1) (hb : d112688 q = 1) : d13789 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d2312, d13789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2312, d13789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d2313 q = 1) (hb : d112688 q = 1) : d13790 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d2313, d13790, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d2313, d13790, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d2314 q = 1) (hb : d112688 q = 1) : d13791 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d2314, d13791, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2314, d13791, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d2315 q = 1) (hb : d112688 q = 1) : d13792 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d2315, d13792, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2315, d13792, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d2316 q = 1) (hb : d112688 q = 1) : d13793 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d2316, d13793, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d2316, d13793, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro18477 (p : Pattern) (ha : d2325 p = 1) (hb : d112688 p = 1) : d13802 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d112688 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d2311 q = 1) (hb : d112688 q = 1) : d13788 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d2311, d13788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18475 q ha hb
    | true =>
      simp only [d2311, d13788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d2312 q = 1) (hb : d112688 q = 1) : d13789 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d2312, d13789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2312, d13789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d2313 q = 1) (hb : d112688 q = 1) : d13790 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d2313, d13790, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d2313, d13790, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d2314 q = 1) (hb : d112688 q = 1) : d13791 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d2314, d13791, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2314, d13791, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d2315 q = 1) (hb : d112688 q = 1) : d13792 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d2315, d13792, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2315, d13792, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d2325 q = 1) (hb : d112688 q = 1) : d13802 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d2325, d13802, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2325, d13802, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro18478 (p : Pattern) (ha : d2385 p = 1) (hb : d112688 p = 1) : d13849 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d94753 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d2367 q = 1) (hb : d94753 q = 1) : d13844 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d2367, d13844, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12673 q ha hb
    | true =>
      simp only [d2367, d13844, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12674 q ha hb
  have h2 (q : Pattern) (ha : d2368 q = 1) (hb : d94753 q = 1) : d13845 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d2368, d13845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2368, d13845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d2369 q = 1) (hb : d94753 q = 1) : d13846 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d2369, d13846, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2369, d13846, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d112686 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d2375 q = 1) (hb : d112687 q = 1) : d13847 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d2375, d112687, d13847, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d2375, d112687, d13847, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d2384 q = 1) (hb : d112688 q = 1) : d13848 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d2384, d112688, d13848, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d2384, d112688, d13848, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d112688 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d2385 q = 1) (hb : d112688 q = 1) : d13849 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d2385, d13849, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d2385, d13849, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro18479 (p : Pattern) (ha : d2452 p = 1) (hb : d112688 p = 1) : d13913 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d112688 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d2386 q = 1) (hb : d112688 q = 1) : d13850 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d2386, d13850, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18478 q ha hb
    | true =>
      simp only [d2386, d13850, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d2387 q = 1) (hb : d112688 q = 1) : d13851 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d2387, d13851, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2387, d13851, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d2449 q = 1) (hb : d112688 q = 1) : d13910 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d2449, d13910, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d2449, d13910, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d2450 q = 1) (hb : d112688 q = 1) : d13911 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d2450, d13911, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d2450, d13911, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d2451 q = 1) (hb : d112688 q = 1) : d13912 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d2451, d13912, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d2451, d13912, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d2452 q = 1) (hb : d112688 q = 1) : d13913 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d2452, d13913, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d2452, d13913, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro18480 (p : Pattern) (ha : d2458 p = 1) (hb : d112688 p = 1) : d13919 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d112688 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d2453 q = 1) (hb : d112688 q = 1) : d13914 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d2453, d13914, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18479 q ha hb
    | true =>
      simp only [d2453, d13914, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d2454 q = 1) (hb : d112688 q = 1) : d13915 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d2454, d13915, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2454, d13915, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d2455 q = 1) (hb : d112688 q = 1) : d13916 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d2455, d13916, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d2455, d13916, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d2456 q = 1) (hb : d112688 q = 1) : d13917 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d2456, d13917, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2456, d13917, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d2457 q = 1) (hb : d112688 q = 1) : d13918 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d2457, d13918, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2457, d13918, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d2458 q = 1) (hb : d112688 q = 1) : d13919 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d2458, d13919, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2458, d13919, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro18481 (p : Pattern) (ha : d8037 p = 1) (hb : d112688 p = 1) : d114838 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d94753 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d2073 q = 1) (hb : d94753 q = 1) : d13610 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d2073, d13610, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12659 q ha hb
    | true =>
      simp only [d2073, d13610, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12636 q ha hb
  have h2 (q : Pattern) (ha : d2074 q = 1) (hb : d94753 q = 1) : d13611 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d2074, d13611, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2074, d13611, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d2075 q = 1) (hb : d94753 q = 1) : d13612 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d2075, d13612, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2075, d13612, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d112686 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d2085 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d2086 q = 1) (hb : d112686 q = 1) : d88948 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d2086, d112686, d88948, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12636 q ha hb
    | true =>
      simp only [d2086, d112686, d88948, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d2087 q = 1) (hb : d112686 q = 1) : d88949 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d2087, d88949, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d2087, d88949, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d2088 q = 1) (hb : d112686 q = 1) : d88950 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d2088, d88950, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d2088, d88950, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d2089 q = 1) (hb : d112687 q = 1) : d114836 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d2089, d112687, d114836, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d2089, d112687, d114836, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d8036 q = 1) (hb : d112688 q = 1) : d114837 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d8036, d112688, d114837, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d8036, d112688, d114837, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d112688 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d8037 q = 1) (hb : d112688 q = 1) : d114838 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d8037, d114838, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d8037, d114838, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  exact h13 p ha hb
theorem andIntro18482 (p : Pattern) (ha : d8043 p = 1) (hb : d112688 p = 1) : d114844 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d112688 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d8038 q = 1) (hb : d112688 q = 1) : d114839 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d8038, d114839, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18481 q ha hb
    | true =>
      simp only [d8038, d114839, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d8039 q = 1) (hb : d112688 q = 1) : d114840 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d8039, d114840, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8039, d114840, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d2097 q = 1) (hb : d112688 q = 1) : d13625 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d2097, d13625, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18473 q ha hb
    | true =>
      simp only [d2097, d13625, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d2098 q = 1) (hb : d112688 q = 1) : d13626 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d2098, d13626, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2098, d13626, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d8040 q = 1) (hb : d112688 q = 1) : d114841 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d8040, d114841, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d8040, d114841, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d8041 q = 1) (hb : d112688 q = 1) : d114842 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d8041, d114842, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d8041, d114842, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d8042 q = 1) (hb : d112688 q = 1) : d114843 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d8042, d114843, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d8042, d114843, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d8043 q = 1) (hb : d112688 q = 1) : d114844 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d8043, d114844, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8043, d114844, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro18483 (p : Pattern) (ha : d8049 p = 1) (hb : d112688 p = 1) : d114850 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d112688 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d8044 q = 1) (hb : d112688 q = 1) : d114845 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d8044, d114845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18482 q ha hb
    | true =>
      simp only [d8044, d114845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18474 q ha hb
  have h2 (q : Pattern) (ha : d8045 q = 1) (hb : d112688 q = 1) : d114846 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d8045, d114846, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8045, d114846, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d8046 q = 1) (hb : d112688 q = 1) : d114847 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d8046, d114847, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d8046, d114847, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d8047 q = 1) (hb : d112688 q = 1) : d114848 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d8047, d114848, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8047, d114848, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d8048 q = 1) (hb : d112688 q = 1) : d114849 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d8048, d114849, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8048, d114849, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d8049 q = 1) (hb : d112688 q = 1) : d114850 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d8049, d114850, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8049, d114850, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro18484 (p : Pattern) (ha : d8052 p = 1) (hb : d112688 p = 1) : d114853 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d112688 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d8038 q = 1) (hb : d112688 q = 1) : d114839 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d8038, d114839, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18481 q ha hb
    | true =>
      simp only [d8038, d114839, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d8039 q = 1) (hb : d112688 q = 1) : d114840 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d8039, d114840, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8039, d114840, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d2097 q = 1) (hb : d112688 q = 1) : d13625 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d2097, d13625, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18473 q ha hb
    | true =>
      simp only [d2097, d13625, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d2098 q = 1) (hb : d112688 q = 1) : d13626 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d2098, d13626, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2098, d13626, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d8040 q = 1) (hb : d112688 q = 1) : d114841 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d8040, d114841, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d8040, d114841, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d8041 q = 1) (hb : d112688 q = 1) : d114842 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d8041, d114842, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d8041, d114842, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d8042 q = 1) (hb : d112688 q = 1) : d114843 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d8042, d114843, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d8042, d114843, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d8052 q = 1) (hb : d112688 q = 1) : d114853 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d8052, d114853, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d8052, d114853, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro18485 (p : Pattern) (ha : d8058 p = 1) (hb : d112688 p = 1) : d114859 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d112688 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d8044 q = 1) (hb : d112688 q = 1) : d114845 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d8044, d114845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18482 q ha hb
    | true =>
      simp only [d8044, d114845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18474 q ha hb
  have h2 (q : Pattern) (ha : d8045 q = 1) (hb : d112688 q = 1) : d114846 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d8045, d114846, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8045, d114846, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d8046 q = 1) (hb : d112688 q = 1) : d114847 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d8046, d114847, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d8046, d114847, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d8047 q = 1) (hb : d112688 q = 1) : d114848 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d8047, d114848, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8047, d114848, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d8048 q = 1) (hb : d112688 q = 1) : d114849 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d8048, d114849, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8048, d114849, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d8053 q = 1) (hb : d112688 q = 1) : d114854 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d8053, d114854, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18484 q ha hb
    | true =>
      simp only [d8053, d114854, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18475 q ha hb
  have h7 (q : Pattern) (ha : d8054 q = 1) (hb : d112688 q = 1) : d114855 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d8054, d114855, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8054, d114855, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d8055 q = 1) (hb : d112688 q = 1) : d114856 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d8055, d114856, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d8055, d114856, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d8056 q = 1) (hb : d112688 q = 1) : d114857 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d8056, d114857, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8056, d114857, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d8057 q = 1) (hb : d112688 q = 1) : d114858 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d8057, d114858, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8057, d114858, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d8058 q = 1) (hb : d112688 q = 1) : d114859 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d8058, d114859, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d8058, d114859, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro18486 (p : Pattern) (ha : d8125 p = 1) (hb : d112688 p = 1) : d114919 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d112688 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d8044 q = 1) (hb : d112688 q = 1) : d114845 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d8044, d114845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18482 q ha hb
    | true =>
      simp only [d8044, d114845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18474 q ha hb
  have h2 (q : Pattern) (ha : d8045 q = 1) (hb : d112688 q = 1) : d114846 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d8045, d114846, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8045, d114846, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d8046 q = 1) (hb : d112688 q = 1) : d114847 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d8046, d114847, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d8046, d114847, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d8047 q = 1) (hb : d112688 q = 1) : d114848 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d8047, d114848, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8047, d114848, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d8048 q = 1) (hb : d112688 q = 1) : d114849 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d8048, d114849, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8048, d114849, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d2305 q = 1) (hb : d112688 q = 1) : d13782 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d2305, d13782, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18474 q ha hb
    | true =>
      simp only [d2305, d13782, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d2306 q = 1) (hb : d112688 q = 1) : d13783 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d2306, d13783, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2306, d13783, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d2307 q = 1) (hb : d112688 q = 1) : d13784 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d2307, d13784, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d2307, d13784, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d2308 q = 1) (hb : d112688 q = 1) : d13785 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d2308, d13785, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2308, d13785, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d2309 q = 1) (hb : d112688 q = 1) : d13786 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d2309, d13786, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2309, d13786, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d8125 q = 1) (hb : d112688 q = 1) : d114919 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d8125, d114919, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d8125, d114919, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro18487 (p : Pattern) (ha : d2129 p = 1) (hb : d112688 p = 1) : d13657 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d112688 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d2097 q = 1) (hb : d112688 q = 1) : d13625 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d2097, d13625, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18473 q ha hb
    | true =>
      simp only [d2097, d13625, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d2098 q = 1) (hb : d112688 q = 1) : d13626 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d2098, d13626, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2098, d13626, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d2103 q = 1) (hb : d112688 q = 1) : d13631 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d2103, d13631, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d2103, d13631, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d2104 q = 1) (hb : d112688 q = 1) : d13632 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d2104, d13632, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d2104, d13632, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d2128 q = 1) (hb : d112688 q = 1) : d13656 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d2128, d13656, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2128, d13656, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d2129 q = 1) (hb : d112688 q = 1) : d13657 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d2129, d13657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2129, d13657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro18488 (p : Pattern) (ha : d2139 p = 1) (hb : d112688 p = 1) : d13667 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d112688 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d2097 q = 1) (hb : d112688 q = 1) : d13625 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d2097, d13625, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18473 q ha hb
    | true =>
      simp only [d2097, d13625, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d2098 q = 1) (hb : d112688 q = 1) : d13626 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d2098, d13626, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2098, d13626, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d2103 q = 1) (hb : d112688 q = 1) : d13631 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d2103, d13631, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d2103, d13631, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d2137 q = 1) (hb : d112688 q = 1) : d13665 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d2137, d13665, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2137, d13665, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d2138 q = 1) (hb : d112688 q = 1) : d13666 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d2138, d13666, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d2138, d13666, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d2139 q = 1) (hb : d112688 q = 1) : d13667 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d2139, d13667, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2139, d13667, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro18489 (p : Pattern) (ha : d8063 p = 1) (hb : d112688 p = 1) : d114864 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d112688 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d8038 q = 1) (hb : d112688 q = 1) : d114839 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d8038, d114839, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18481 q ha hb
    | true =>
      simp only [d8038, d114839, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d8039 q = 1) (hb : d112688 q = 1) : d114840 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d8039, d114840, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8039, d114840, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d2097 q = 1) (hb : d112688 q = 1) : d13625 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d2097, d13625, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18473 q ha hb
    | true =>
      simp only [d2097, d13625, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d2098 q = 1) (hb : d112688 q = 1) : d13626 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d2098, d13626, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2098, d13626, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d8040 q = 1) (hb : d112688 q = 1) : d114841 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d8040, d114841, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d8040, d114841, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d8041 q = 1) (hb : d112688 q = 1) : d114842 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d8041, d114842, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d8041, d114842, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d8062 q = 1) (hb : d112688 q = 1) : d114863 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d8062, d114863, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8062, d114863, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d8063 q = 1) (hb : d112688 q = 1) : d114864 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d8063, d114864, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8063, d114864, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro18490 (p : Pattern) (ha : d8070 p = 1) (hb : d112688 p = 1) : d114871 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d112688 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d8038 q = 1) (hb : d112688 q = 1) : d114839 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d8038, d114839, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18481 q ha hb
    | true =>
      simp only [d8038, d114839, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d8039 q = 1) (hb : d112688 q = 1) : d114840 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d8039, d114840, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8039, d114840, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d2097 q = 1) (hb : d112688 q = 1) : d13625 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d2097, d13625, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18473 q ha hb
    | true =>
      simp only [d2097, d13625, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d2098 q = 1) (hb : d112688 q = 1) : d13626 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d2098, d13626, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2098, d13626, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d8040 q = 1) (hb : d112688 q = 1) : d114841 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d8040, d114841, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d8040, d114841, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d8068 q = 1) (hb : d112688 q = 1) : d114869 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d8068, d114869, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8068, d114869, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d8069 q = 1) (hb : d112688 q = 1) : d114870 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d8069, d114870, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d8069, d114870, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d8070 q = 1) (hb : d112688 q = 1) : d114871 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d8070, d114871, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8070, d114871, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro18491 (p : Pattern) (ha : d2149 p = 1) (hb : d94753 p = 1) : d13671 p = 1 := by
  have h0 (q : Pattern) (ha : d1 q = 1) (hb : d2148 q = 1) : d2148 q = 1 := by
    exact hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d2057 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d2149 q = 1) (hb : d94753 q = 1) : d13671 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d2149, d94753, d13671, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d2149, d94753, d13671, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  exact h2 p ha hb
theorem andIntro18492 (p : Pattern) (ha : d8075 p = 1) (hb : d112688 p = 1) : d114880 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d94753 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d2150 q = 1) (hb : d94753 q = 1) : d13672 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d2150, d13672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18491 q ha hb
    | true =>
      simp only [d2150, d13672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12659 q ha hb
  have h2 (q : Pattern) (ha : d2151 q = 1) (hb : d94753 q = 1) : d13673 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d2151, d13673, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2151, d13673, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d2152 q = 1) (hb : d94753 q = 1) : d13674 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d2152, d13674, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2152, d13674, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d112686 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d2072 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d2073 q = 1) (hb : d112686 q = 1) : d114875 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d2073, d112686, d114875, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12659 q ha hb
    | true =>
      simp only [d2073, d112686, d114875, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d2074 q = 1) (hb : d112686 q = 1) : d114876 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d2074, d114876, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d2074, d114876, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d2075 q = 1) (hb : d112686 q = 1) : d114877 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d2075, d114877, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d2075, d114877, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d2153 q = 1) (hb : d112687 q = 1) : d114878 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d2153, d112687, d114878, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d2153, d112687, d114878, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d8074 q = 1) (hb : d112688 q = 1) : d114879 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d8074, d112688, d114879, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d8074, d112688, d114879, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d112688 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d8075 q = 1) (hb : d112688 q = 1) : d114880 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d8075, d114880, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d8075, d114880, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  exact h13 p ha hb
theorem andIntro18493 (p : Pattern) (ha : d8081 p = 1) (hb : d112688 p = 1) : d114886 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d112688 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d8076 q = 1) (hb : d112688 q = 1) : d114881 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d8076, d114881, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18492 q ha hb
    | true =>
      simp only [d8076, d114881, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d8077 q = 1) (hb : d112688 q = 1) : d114882 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d8077, d114882, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8077, d114882, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d8038 q = 1) (hb : d112688 q = 1) : d114839 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d8038, d114839, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18481 q ha hb
    | true =>
      simp only [d8038, d114839, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d8039 q = 1) (hb : d112688 q = 1) : d114840 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d8039, d114840, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8039, d114840, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d8078 q = 1) (hb : d112688 q = 1) : d114883 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d8078, d114883, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d8078, d114883, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d8079 q = 1) (hb : d112688 q = 1) : d114884 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d8079, d114884, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d8079, d114884, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d8080 q = 1) (hb : d112688 q = 1) : d114885 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d8080, d114885, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d8080, d114885, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d8081 q = 1) (hb : d112688 q = 1) : d114886 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d8081, d114886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8081, d114886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro18494 (p : Pattern) (ha : d8096 p = 1) (hb : d112688 p = 1) : d114892 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d112688 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d8038 q = 1) (hb : d112688 q = 1) : d114839 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d8038, d114839, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18481 q ha hb
    | true =>
      simp only [d8038, d114839, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d8039 q = 1) (hb : d112688 q = 1) : d114840 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d8039, d114840, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8039, d114840, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d8093 q = 1) (hb : d112688 q = 1) : d114889 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d8093, d114889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d8093, d114889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d8094 q = 1) (hb : d112688 q = 1) : d114890 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d8094, d114890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d8094, d114890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d8095 q = 1) (hb : d112688 q = 1) : d114891 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d8095, d114891, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d8095, d114891, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d8096 q = 1) (hb : d112688 q = 1) : d114892 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d8096, d114892, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8096, d114892, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro18495 (p : Pattern) (ha : d85637 p = 1) (hb : d112688 p = 1) : d114898 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d112688 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d8064 q = 1) (hb : d112688 q = 1) : d114865 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d8064, d114865, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18489 q ha hb
    | true =>
      simp only [d8064, d114865, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18487 q ha hb
  have h2 (q : Pattern) (ha : d8065 q = 1) (hb : d112688 q = 1) : d114866 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d8065, d114866, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8065, d114866, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d8066 q = 1) (hb : d112688 q = 1) : d114867 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d8066, d114867, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d8066, d114867, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d8067 q = 1) (hb : d112688 q = 1) : d114868 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d8067, d114868, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8067, d114868, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d8071 q = 1) (hb : d112688 q = 1) : d114872 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d8071, d114872, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18490 q ha hb
    | true =>
      simp only [d8071, d114872, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18488 q ha hb
  have h6 (q : Pattern) (ha : d8072 q = 1) (hb : d112688 q = 1) : d114873 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d8072, d114873, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8072, d114873, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d8073 q = 1) (hb : d112688 q = 1) : d114874 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d8073, d114874, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d8073, d114874, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d8082 q = 1) (hb : d112688 q = 1) : d114887 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d8082, d114887, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18493 q ha hb
    | true =>
      simp only [d8082, d114887, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18482 q ha hb
  have h9 (q : Pattern) (ha : d85633 q = 1) (hb : d112688 q = 1) : d114888 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d85633, d114888, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d85633, d114888, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d8097 q = 1) (hb : d112688 q = 1) : d114893 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d8097, d114893, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18494 q ha hb
    | true =>
      simp only [d8097, d114893, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d8098 q = 1) (hb : d112688 q = 1) : d114894 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d8098, d114894, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d8098, d114894, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d85634 q = 1) (hb : d112688 q = 1) : d114895 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d85634, d114895, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d85634, d114895, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d85635 q = 1) (hb : d112688 q = 1) : d114896 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d85635, d114896, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d85635, d114896, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d85636 q = 1) (hb : d112688 q = 1) : d114897 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d85636, d114897, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d85636, d114897, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d85637 q = 1) (hb : d112688 q = 1) : d114898 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d85637, d114898, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d85637, d114898, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro18496 (p : Pattern) (ha : d2282 p = 1) (hb : d112688 p = 1) : d13752 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d112688 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d2097 q = 1) (hb : d112688 q = 1) : d13625 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d2097, d13625, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18473 q ha hb
    | true =>
      simp only [d2097, d13625, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d2098 q = 1) (hb : d112688 q = 1) : d13626 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d2098, d13626, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2098, d13626, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d2103 q = 1) (hb : d112688 q = 1) : d13631 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d2103, d13631, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d2103, d13631, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d2104 q = 1) (hb : d112688 q = 1) : d13632 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d2104, d13632, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d2104, d13632, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d2128 q = 1) (hb : d112688 q = 1) : d13656 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d2128, d13656, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2128, d13656, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d2282 q = 1) (hb : d112688 q = 1) : d13752 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d2282, d13752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d2282, d13752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro18497 (p : Pattern) (ha : d2288 p = 1) (hb : d112688 p = 1) : d13758 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d112688 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d2097 q = 1) (hb : d112688 q = 1) : d13625 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d2097, d13625, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18473 q ha hb
    | true =>
      simp only [d2097, d13625, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d2098 q = 1) (hb : d112688 q = 1) : d13626 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d2098, d13626, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2098, d13626, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d2103 q = 1) (hb : d112688 q = 1) : d13631 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d2103, d13631, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d2103, d13631, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d2137 q = 1) (hb : d112688 q = 1) : d13665 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d2137, d13665, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2137, d13665, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d2138 q = 1) (hb : d112688 q = 1) : d13666 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d2138, d13666, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d2138, d13666, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d2288 q = 1) (hb : d112688 q = 1) : d13758 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d2288, d13758, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d2288, d13758, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro18498 (p : Pattern) (ha : d8103 p = 1) (hb : d112688 p = 1) : d114899 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d112688 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d8038 q = 1) (hb : d112688 q = 1) : d114839 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d8038, d114839, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18481 q ha hb
    | true =>
      simp only [d8038, d114839, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d8039 q = 1) (hb : d112688 q = 1) : d114840 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d8039, d114840, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8039, d114840, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d2097 q = 1) (hb : d112688 q = 1) : d13625 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d2097, d13625, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18473 q ha hb
    | true =>
      simp only [d2097, d13625, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d2098 q = 1) (hb : d112688 q = 1) : d13626 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d2098, d13626, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2098, d13626, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d8040 q = 1) (hb : d112688 q = 1) : d114841 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d8040, d114841, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d8040, d114841, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d8041 q = 1) (hb : d112688 q = 1) : d114842 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d8041, d114842, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d8041, d114842, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d8062 q = 1) (hb : d112688 q = 1) : d114863 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d8062, d114863, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8062, d114863, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d8103 q = 1) (hb : d112688 q = 1) : d114899 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d8103, d114899, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d8103, d114899, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro18499 (p : Pattern) (ha : d8108 p = 1) (hb : d112688 p = 1) : d114904 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d112688 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d8038 q = 1) (hb : d112688 q = 1) : d114839 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d8038, d114839, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18481 q ha hb
    | true =>
      simp only [d8038, d114839, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d8039 q = 1) (hb : d112688 q = 1) : d114840 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d8039, d114840, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8039, d114840, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d2097 q = 1) (hb : d112688 q = 1) : d13625 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d2097, d13625, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18473 q ha hb
    | true =>
      simp only [d2097, d13625, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d2098 q = 1) (hb : d112688 q = 1) : d13626 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d2098, d13626, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2098, d13626, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d8040 q = 1) (hb : d112688 q = 1) : d114841 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d8040, d114841, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d8040, d114841, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d8068 q = 1) (hb : d112688 q = 1) : d114869 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d8068, d114869, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8068, d114869, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d8069 q = 1) (hb : d112688 q = 1) : d114870 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d8069, d114870, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d8069, d114870, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d8108 q = 1) (hb : d112688 q = 1) : d114904 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d8108, d114904, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d8108, d114904, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
end NetHack.Soko22Hazard87
