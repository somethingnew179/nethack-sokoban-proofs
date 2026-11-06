import NetHack.Soko22Hazard87.AndIntroBlocks0410
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Soko22Hazard87
open NetHack.Sokoban NetHack.Sokoban.PatternCorrection
theorem andIntro102750 (p : Pattern) (ha : d269108 p = 1) (hb : d332562 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d269076 q = 1) (hb : d332530 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d269076, d332530, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro102742 q ha hb
    | true =>
      simp only [d269076, d332530, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d269077 q = 1) (hb : d332531 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d269077, d332531, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d269077, d332531, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d269082 q = 1) (hb : d332536 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d269082, d332536, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d269082, d332536, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d269083 q = 1) (hb : d332537 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d269083, d332537, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d269083, d332537, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d269107 q = 1) (hb : d332561 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d269107, d332561, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d269107, d332561, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d269108 q = 1) (hb : d332562 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d269108, d332562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d269108, d332562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro102751 (p : Pattern) (ha : d269115 p = 1) (hb : d332569 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d269072 q = 1) (hb : d332526 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d269072, d332526, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro102741 q ha hb
    | true =>
      simp only [d269072, d332526, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d269073 q = 1) (hb : d332527 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d269073, d332527, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d269073, d332527, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d269076 q = 1) (hb : d332530 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d269076, d332530, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro102742 q ha hb
    | true =>
      simp only [d269076, d332530, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d269077 q = 1) (hb : d332531 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d269077, d332531, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d269077, d332531, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d269078 q = 1) (hb : d332532 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d269078, d332532, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d269078, d332532, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d269113 q = 1) (hb : d332567 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d269113, d332567, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d269113, d332567, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d269114 q = 1) (hb : d332568 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d269114, d332568, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d269114, d332568, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d269115 q = 1) (hb : d332569 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d269115, d332569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d269115, d332569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro102752 (p : Pattern) (ha : d269118 p = 1) (hb : d332572 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d269076 q = 1) (hb : d332530 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d269076, d332530, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro102742 q ha hb
    | true =>
      simp only [d269076, d332530, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d269077 q = 1) (hb : d332531 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d269077, d332531, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d269077, d332531, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d269082 q = 1) (hb : d332536 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d269082, d332536, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d269082, d332536, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d269116 q = 1) (hb : d332570 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d269116, d332570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d269116, d332570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d269117 q = 1) (hb : d332571 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d269117, d332571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d269117, d332571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d269118 q = 1) (hb : d332572 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d269118, d332572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d269118, d332572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro102753 (p : Pattern) (ha : d269124 p = 1) (hb : d312057 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d269123 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d268385 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d2008 q = 1) (hb : d268959 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d2008, d268959, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d2008, d268959, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro257 q ha hb
  have h4 (q : Pattern) (ha : d34782 q = 1) (hb : d268960 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d34782, d268960, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d34782, d268960, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h5 (q : Pattern) (ha : d34783 q = 1) (hb : d268961 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d34783, d268961, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d34783, d268961, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d268387 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d43846 q = 1) (hb : d268964 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d43846, d268964, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro102727 q ha hb
    | true =>
      simp only [d43846, d268964, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h8 (q : Pattern) (ha : d43847 q = 1) (hb : d268965 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d43847, d268965, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d43847, d268965, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h9 (q : Pattern) (ha : d43848 q = 1) (hb : d268966 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d43848, d268966, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d43848, d268966, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d268967 q = 1) (hb : d311925 q = 1) : d0 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d268967, d311925, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
    | true =>
      simp only [d268967, d311925, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
  have h11 (q : Pattern) (ha : d268968 q = 1) (hb : d311926 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d268968, d311926, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d268968, d311926, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h12 (q : Pattern) (ha : d269124 q = 1) (hb : d312057 q = 1) : d0 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d269124, d312057, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d269124, d312057, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  exact h12 p ha hb
theorem andIntro102754 (p : Pattern) (ha : d269129 p = 1) (hb : d332576 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d268385 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d2008 q = 1) (hb : d268959 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d2008, d268959, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d2008, d268959, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro257 q ha hb
  have h3 (q : Pattern) (ha : d34782 q = 1) (hb : d268960 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d34782, d268960, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d34782, d268960, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d34783 q = 1) (hb : d268961 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d34783, d268961, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d34783, d268961, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d268387 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d43846 q = 1) (hb : d268964 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d43846, d268964, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro102727 q ha hb
    | true =>
      simp only [d43846, d268964, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d43847 q = 1) (hb : d268965 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d43847, d268965, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d43847, d268965, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d43848 q = 1) (hb : d268966 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d43848, d268966, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d43848, d268966, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d268967 q = 1) (hb : d311925 q = 1) : d0 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d268967, d311925, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d268967, d311925, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d268968 q = 1) (hb : d311926 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d268968, d311926, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d268968, d311926, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h11 (q : Pattern) (ha : d269129 q = 1) (hb : d332576 q = 1) : d0 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d269129, d332576, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d269129, d332576, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h11 p ha hb
theorem andIntro102755 (p : Pattern) (ha : d269136 p = 1) (hb : d332583 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d269125 q = 1) (hb : d312058 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d269125, d312058, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro102753 q ha hb
    | true =>
      simp only [d269125, d312058, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d269126 q = 1) (hb : d312059 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d269126, d312059, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d269126, d312059, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d269127 q = 1) (hb : d312060 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d269127, d312060, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d269127, d312060, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d269128 q = 1) (hb : d312061 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d269128, d312061, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d269128, d312061, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d269130 q = 1) (hb : d332577 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d269130, d332577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro102754 q ha hb
    | true =>
      simp only [d269130, d332577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d269131 q = 1) (hb : d332578 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d269131, d332578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d269131, d332578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d269132 q = 1) (hb : d332579 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d269132, d332579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d269132, d332579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d269133 q = 1) (hb : d332580 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d269133, d332580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d269133, d332580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d269134 q = 1) (hb : d332581 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d269134, d332581, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d269134, d332581, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d268997 q = 1) (hb : d332479 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d268997, d332479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro102732 q ha hb
    | true =>
      simp only [d268997, d332479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h11 (q : Pattern) (ha : d268998 q = 1) (hb : d332480 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d268998, d332480, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d268998, d332480, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d268999 q = 1) (hb : d332481 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d268999, d332481, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d268999, d332481, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d269000 q = 1) (hb : d332482 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d269000, d332482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d269000, d332482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h14 (q : Pattern) (ha : d269135 q = 1) (hb : d332582 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d269135, d332582, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d269135, d332582, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d269136 q = 1) (hb : d332583 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d269136, d332583, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d269136, d332583, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro102756 (p : Pattern) (ha : d269143 p = 1) (hb : d332587 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d268385 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d2008 q = 1) (hb : d268959 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d2008, d268959, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2008, d268959, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro257 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d34782 q = 1) (hb : d268960 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d34782, d268960, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d34782, d268960, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d10055 q = 1) (hb : d101482 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d10055, d101482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d10055, d101482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23340 q ha hb
  have h5 (q : Pattern) (ha : d10056 q = 1) (hb : d101483 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d10056, d101483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d10056, d101483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h6 (q : Pattern) (ha : d269140 q = 1) (hb : d278981 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d269140, d278981, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d269140, d278981, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d269141 q = 1) (hb : d278982 q = 1) : d0 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d269141, d278982, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d269141, d278982, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h8 (q : Pattern) (ha : d269142 q = 1) (hb : d278983 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d269142, d278983, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d269142, d278983, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h9 (q : Pattern) (ha : d32155 q = 1) (hb : d242968 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d32155, d242968, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d32155, d242968, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23312 q ha hb
  have h10 (q : Pattern) (ha : d37519 q = 1) (hb : d268983 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d37519, d268983, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d37519, d268983, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d101484 q = 1) (hb : d332459 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d101484, d332459, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro102730 q hb ha
    | true =>
      simp only [d101484, d332459, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h12 (q : Pattern) (ha : d101485 q = 1) (hb : d332460 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d101485, d332460, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d101485, d332460, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h13 (q : Pattern) (ha : d268984 q = 1) (hb : d332469 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d268984, d332469, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
    | true =>
      simp only [d268984, d332469, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d268985 q = 1) (hb : d332470 q = 1) : d0 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d268985, d332470, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d268985, d332470, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h15 (q : Pattern) (ha : d268986 q = 1) (hb : d332471 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d268986, d332471, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d268986, d332471, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h16 (q : Pattern) (ha : d269143 q = 1) (hb : d332587 q = 1) : d0 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d269143, d332587, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d269143, d332587, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  exact h16 p ha hb
theorem andIntro102757 (p : Pattern) (ha : d269149 p = 1) (hb : d332593 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d269144 q = 1) (hb : d332588 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d269144, d332588, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro102756 q ha hb
    | true =>
      simp only [d269144, d332588, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d269145 q = 1) (hb : d332589 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d269145, d332589, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d269145, d332589, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d269146 q = 1) (hb : d332590 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d269146, d332590, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d269146, d332590, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d269147 q = 1) (hb : d332591 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d269147, d332591, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d269147, d332591, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d269013 q = 1) (hb : d332489 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d269013, d332489, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro102733 q ha hb
    | true =>
      simp only [d269013, d332489, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d269014 q = 1) (hb : d332490 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d269014, d332490, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d269014, d332490, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d269015 q = 1) (hb : d332491 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d269015, d332491, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d269015, d332491, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d269016 q = 1) (hb : d332492 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d269016, d332492, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d269016, d332492, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d269148 q = 1) (hb : d332592 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d269148, d332592, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d269148, d332592, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d269036 q = 1) (hb : d332512 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d269036, d332512, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d269036, d332512, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h11 (q : Pattern) (ha : d269149 q = 1) (hb : d332593 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d269149, d332593, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d269149, d332593, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro102758 (p : Pattern) (ha : d269155 p = 1) (hb : d332599 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d269137 q = 1) (hb : d332584 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d269137, d332584, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro102755 q ha hb
    | true =>
      simp only [d269137, d332584, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro102734 q ha hb
  have h2 (q : Pattern) (ha : d269138 q = 1) (hb : d332585 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d269138, d332585, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d269138, d332585, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d269139 q = 1) (hb : d332586 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d269139, d332586, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d269139, d332586, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d269150 q = 1) (hb : d332594 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d269150, d332594, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro102734 q ha hb
    | true =>
      simp only [d269150, d332594, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro102757 q ha hb
  have h5 (q : Pattern) (ha : d269151 q = 1) (hb : d332595 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d269151, d332595, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d269151, d332595, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d269152 q = 1) (hb : d332596 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d269152, d332596, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d269152, d332596, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d269153 q = 1) (hb : d332597 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d269153, d332597, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d269153, d332597, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d269038 q = 1) (hb : d332514 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d269038, d332514, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro102734 q ha hb
    | true =>
      simp only [d269038, d332514, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro102737 q ha hb
  have h9 (q : Pattern) (ha : d269039 q = 1) (hb : d332515 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d269039, d332515, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d269039, d332515, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d269040 q = 1) (hb : d332516 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d269040, d332516, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d269040, d332516, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d269060 q = 1) (hb : d332519 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d269060, d332519, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro102737 q ha hb
    | true =>
      simp only [d269060, d332519, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro102739 q ha hb
  have h12 (q : Pattern) (ha : d269061 q = 1) (hb : d332520 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d269061, d332520, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d269061, d332520, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d269062 q = 1) (hb : d332521 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d269062, d332521, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d269062, d332521, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d269063 q = 1) (hb : d332522 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d269063, d332522, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d269063, d332522, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d269154 q = 1) (hb : d332598 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d269154, d332598, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d269154, d332598, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d269155 q = 1) (hb : d332599 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d269155, d332599, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d269155, d332599, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h16 p ha hb
theorem andIntro102759 (p : Pattern) (ha : d269160 p = 1) (hb : d332525 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d269038 q = 1) (hb : d332514 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d269038, d332514, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro102734 q ha hb
    | true =>
      simp only [d269038, d332514, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro102737 q ha hb
  have h2 (q : Pattern) (ha : d269039 q = 1) (hb : d332515 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d269039, d332515, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d269039, d332515, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d269040 q = 1) (hb : d332516 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d269040, d332516, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d269040, d332516, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d269060 q = 1) (hb : d332519 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d269060, d332519, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro102737 q ha hb
    | true =>
      simp only [d269060, d332519, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro102739 q ha hb
  have h5 (q : Pattern) (ha : d269061 q = 1) (hb : d332520 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d269061, d332520, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d269061, d332520, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d269062 q = 1) (hb : d332521 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d269062, d332521, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d269062, d332521, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d269063 q = 1) (hb : d332522 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d269063, d332522, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d269063, d332522, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d269158 q = 1) (hb : d332523 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d269158, d332523, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d269158, d332523, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d269159 q = 1) (hb : d332524 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d269159, d332524, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d269159, d332524, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d269160 q = 1) (hb : d332525 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d269160, d332525, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d269160, d332525, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h10 p ha hb
theorem andIntro102760 (p : Pattern) (ha : d269166 p = 1) (hb : d332605 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d269156 q = 1) (hb : d332600 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d269156, d332600, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro102758 q ha hb
    | true =>
      simp only [d269156, d332600, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d269157 q = 1) (hb : d332601 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d269157, d332601, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d269157, d332601, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d269161 q = 1) (hb : d332526 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d269161, d332526, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro102759 q ha hb
    | true =>
      simp only [d269161, d332526, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d269162 q = 1) (hb : d332527 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d269162, d332527, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d269162, d332527, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d269163 q = 1) (hb : d332602 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d269163, d332602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d269163, d332602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d269164 q = 1) (hb : d332603 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d269164, d332603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d269164, d332603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d269165 q = 1) (hb : d332604 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d269165, d332604, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d269165, d332604, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d269166 q = 1) (hb : d332605 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d269166, d332605, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d269166, d332605, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro102761 (p : Pattern) (ha : d269170 p = 1) (hb : d332535 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d269161 q = 1) (hb : d332526 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d269161, d332526, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro102759 q ha hb
    | true =>
      simp only [d269161, d332526, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d269162 q = 1) (hb : d332527 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d269162, d332527, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d269162, d332527, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d269076 q = 1) (hb : d332530 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d269076, d332530, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro102742 q ha hb
    | true =>
      simp only [d269076, d332530, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d269077 q = 1) (hb : d332531 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d269077, d332531, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d269077, d332531, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d269167 q = 1) (hb : d332532 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d269167, d332532, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d269167, d332532, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d269168 q = 1) (hb : d332533 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d269168, d332533, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d269168, d332533, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d269169 q = 1) (hb : d332534 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d269169, d332534, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d269169, d332534, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d269170 q = 1) (hb : d332535 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d269170, d332535, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d269170, d332535, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro102762 (p : Pattern) (ha : d269173 p = 1) (hb : d332608 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d268969 q = 1) (hb : d332456 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d268969, d332456, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro102727 q hb ha
    | true =>
      simp only [d268969, d332456, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro68439 q hb ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d32155 q = 1) (hb : d242968 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d32155, d242968, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d32155, d242968, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23312 q ha hb
  have h3 (q : Pattern) (ha : d269001 q = 1) (hb : d332483 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d269001, d332483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d269001, d332483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d101484 q = 1) (hb : d332459 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d101484, d332459, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro102730 q hb ha
    | true =>
      simp only [d101484, d332459, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h5 (q : Pattern) (ha : d101485 q = 1) (hb : d332460 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d101485, d332460, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d101485, d332460, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h6 (q : Pattern) (ha : d269002 q = 1) (hb : d332484 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d269002, d332484, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d269002, d332484, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d268973 q = 1) (hb : d332459 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d268973, d332459, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro102728 q hb ha
    | true =>
      simp only [d268973, d332459, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h8 (q : Pattern) (ha : d268974 q = 1) (hb : d332460 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d268974, d332460, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d268974, d332460, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h9 (q : Pattern) (ha : d269003 q = 1) (hb : d332485 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d269003, d332485, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d269003, d332485, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h10 (q : Pattern) (ha : d269004 q = 1) (hb : d332486 q = 1) : d0 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d269004, d332486, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d269004, d332486, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d269005 q = 1) (hb : d332487 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d269005, d332487, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d269005, d332487, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h12 (q : Pattern) (ha : d5128 q = 1) (hb : d69215 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d5128, d69215, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d5128, d69215, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro207 q ha hb
  have h13 (q : Pattern) (ha : d5129 q = 1) (hb : d69216 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d5129, d69216, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d5129, d69216, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h14 (q : Pattern) (ha : d1564 q = 1) (hb : d53005 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d1564, d53005, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro207 q ha hb
    | true =>
      simp only [d1564, d53005, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h15 (q : Pattern) (ha : d1565 q = 1) (hb : d53006 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d1565, d53006, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d1565, d53006, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h16 (q : Pattern) (ha : d5130 q = 1) (hb : d69217 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d5130, d69217, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d5130, d69217, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d1578 q = 1) (hb : d53019 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d1578, d53019, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d1578, d53019, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h18 (q : Pattern) (ha : d5131 q = 1) (hb : d69218 q = 1) : d0 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d5131, d69218, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d5131, d69218, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d5132 q = 1) (hb : d69219 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d5132, d69219, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d5132, d69219, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h20 (q : Pattern) (ha : d269173 q = 1) (hb : d332608 q = 1) : d0 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d269173, d332608, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d269173, d332608, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q hb ha
  exact h20 p ha hb
theorem andIntro102763 (p : Pattern) (ha : d269179 p = 1) (hb : d332614 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d269026 q = 1) (hb : d332502 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d269026, d332502, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro102735 q ha hb
    | true =>
      simp only [d269026, d332502, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d269027 q = 1) (hb : d332503 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d269027, d332503, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d269027, d332503, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d269028 q = 1) (hb : d332504 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d269028, d332504, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d269028, d332504, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d269029 q = 1) (hb : d332505 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d269029, d332505, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d269029, d332505, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d269031 q = 1) (hb : d332507 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d269031, d332507, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro102736 q ha hb
    | true =>
      simp only [d269031, d332507, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d269032 q = 1) (hb : d332508 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d269032, d332508, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d269032, d332508, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d269033 q = 1) (hb : d332509 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d269033, d332509, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d269033, d332509, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d269034 q = 1) (hb : d332510 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d269034, d332510, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d269034, d332510, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d269035 q = 1) (hb : d332511 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d269035, d332511, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d269035, d332511, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d269174 q = 1) (hb : d332609 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d269174, d332609, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro102762 q ha hb
    | true =>
      simp only [d269174, d332609, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h11 (q : Pattern) (ha : d269175 q = 1) (hb : d332610 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d269175, d332610, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d269175, d332610, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d269176 q = 1) (hb : d332611 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d269176, d332611, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d269176, d332611, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d269177 q = 1) (hb : d332612 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d269177, d332612, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d269177, d332612, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h14 (q : Pattern) (ha : d269178 q = 1) (hb : d332613 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d269178, d332613, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d269178, d332613, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h15 (q : Pattern) (ha : d269179 q = 1) (hb : d332614 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d269179, d332614, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d269179, d332614, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro102764 (p : Pattern) (ha : d269180 p = 1) (hb : d332615 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d268969 q = 1) (hb : d332456 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d268969, d332456, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro102727 q hb ha
    | true =>
      simp only [d268969, d332456, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro68439 q hb ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d32155 q = 1) (hb : d242968 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d32155, d242968, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d32155, d242968, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23312 q ha hb
  have h3 (q : Pattern) (ha : d269001 q = 1) (hb : d332483 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d269001, d332483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d269001, d332483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d269019 q = 1) (hb : d332495 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d269019, d332495, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro102728 q hb ha
    | true =>
      simp only [d269019, d332495, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro207 q hb ha
  have h5 (q : Pattern) (ha : d269020 q = 1) (hb : d332496 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d269020, d332496, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d269020, d332496, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h6 (q : Pattern) (ha : d269021 q = 1) (hb : d332497 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d269021, d332497, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d269021, d332497, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d268973 q = 1) (hb : d332459 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d268973, d332459, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro102728 q hb ha
    | true =>
      simp only [d268973, d332459, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h8 (q : Pattern) (ha : d268974 q = 1) (hb : d332460 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d268974, d332460, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d268974, d332460, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h9 (q : Pattern) (ha : d1564 q = 1) (hb : d53005 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d1564, d53005, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro207 q ha hb
    | true =>
      simp only [d1564, d53005, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h10 (q : Pattern) (ha : d1565 q = 1) (hb : d53006 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d1565, d53006, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d1565, d53006, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h11 (q : Pattern) (ha : d269022 q = 1) (hb : d332498 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d269022, d332498, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d269022, d332498, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
  have h12 (q : Pattern) (ha : d269023 q = 1) (hb : d332499 q = 1) : d0 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d269023, d332499, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d269023, d332499, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d269024 q = 1) (hb : d332500 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d269024, d332500, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d269024, d332500, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h14 (q : Pattern) (ha : d5128 q = 1) (hb : d69215 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d5128, d69215, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d5128, d69215, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro207 q ha hb
  have h15 (q : Pattern) (ha : d5129 q = 1) (hb : d69216 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d5129, d69216, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d5129, d69216, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h16 (q : Pattern) (ha : d5130 q = 1) (hb : d69217 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d5130, d69217, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d5130, d69217, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h17 (q : Pattern) (ha : d1578 q = 1) (hb : d53019 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d1578, d53019, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d1578, d53019, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h18 (q : Pattern) (ha : d5131 q = 1) (hb : d69218 q = 1) : d0 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d5131, d69218, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d5131, d69218, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d5132 q = 1) (hb : d69219 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d5132, d69219, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d5132, d69219, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h20 (q : Pattern) (ha : d269180 q = 1) (hb : d332615 q = 1) : d0 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d269180, d332615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d269180, d332615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q hb ha
  exact h20 p ha hb
theorem andIntro102765 (p : Pattern) (ha : d269186 p = 1) (hb : d332621 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d269181 q = 1) (hb : d332616 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d269181, d332616, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro102764 q ha hb
    | true =>
      simp only [d269181, d332616, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d269182 q = 1) (hb : d332617 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d269182, d332617, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d269182, d332617, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d269183 q = 1) (hb : d332618 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d269183, d332618, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d269183, d332618, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d269184 q = 1) (hb : d332619 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d269184, d332619, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d269184, d332619, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d269185 q = 1) (hb : d332620 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d269185, d332620, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d269185, d332620, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d269186 q = 1) (hb : d332621 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d269186, d332621, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d269186, d332621, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro102766 (p : Pattern) (ha : d269192 p = 1) (hb : d332627 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d269038 q = 1) (hb : d332514 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d269038, d332514, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro102734 q ha hb
    | true =>
      simp only [d269038, d332514, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro102737 q ha hb
  have h2 (q : Pattern) (ha : d269039 q = 1) (hb : d332515 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d269039, d332515, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d269039, d332515, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d269040 q = 1) (hb : d332516 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d269040, d332516, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d269040, d332516, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d269060 q = 1) (hb : d332519 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d269060, d332519, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro102737 q ha hb
    | true =>
      simp only [d269060, d332519, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro102739 q ha hb
  have h5 (q : Pattern) (ha : d269061 q = 1) (hb : d332520 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d269061, d332520, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d269061, d332520, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d269062 q = 1) (hb : d332521 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d269062, d332521, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d269062, d332521, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d269063 q = 1) (hb : d332522 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d269063, d332522, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d269063, d332522, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d269187 q = 1) (hb : d332622 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d269187, d332622, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro102763 q ha hb
    | true =>
      simp only [d269187, d332622, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro102765 q ha hb
  have h9 (q : Pattern) (ha : d269188 q = 1) (hb : d332623 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d269188, d332623, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d269188, d332623, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d269189 q = 1) (hb : d332624 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d269189, d332624, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d269189, d332624, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d269190 q = 1) (hb : d332625 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d269190, d332625, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d269190, d332625, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d269191 q = 1) (hb : d332626 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d269191, d332626, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d269191, d332626, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d269192 q = 1) (hb : d332627 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d269192, d332627, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d269192, d332627, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h13 p ha hb
theorem andIntro102767 (p : Pattern) (ha : d269198 p = 1) (hb : d332633 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d269193 q = 1) (hb : d332628 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d269193, d332628, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro102766 q ha hb
    | true =>
      simp only [d269193, d332628, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d269194 q = 1) (hb : d332629 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d269194, d332629, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d269194, d332629, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d269195 q = 1) (hb : d332630 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d269195, d332630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d269195, d332630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d269196 q = 1) (hb : d332631 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d269196, d332631, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d269196, d332631, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d269197 q = 1) (hb : d332632 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d269197, d332632, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d269197, d332632, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d269198 q = 1) (hb : d332633 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d269198, d332633, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d269198, d332633, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro102768 (p : Pattern) (ha : d269204 p = 1) (hb : d332639 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d269109 q = 1) (hb : d332563 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d269109, d332563, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro102749 q ha hb
    | true =>
      simp only [d269109, d332563, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro102750 q ha hb
  have h2 (q : Pattern) (ha : d269110 q = 1) (hb : d332564 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d269110, d332564, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d269110, d332564, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d269111 q = 1) (hb : d332565 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d269111, d332565, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d269111, d332565, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d269112 q = 1) (hb : d332566 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d269112, d332566, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d269112, d332566, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d269119 q = 1) (hb : d332573 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d269119, d332573, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro102751 q ha hb
    | true =>
      simp only [d269119, d332573, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro102752 q ha hb
  have h6 (q : Pattern) (ha : d269120 q = 1) (hb : d332574 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d269120, d332574, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d269120, d332574, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d269121 q = 1) (hb : d332575 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d269121, d332575, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d269121, d332575, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d269171 q = 1) (hb : d332606 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d269171, d332606, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro102760 q ha hb
    | true =>
      simp only [d269171, d332606, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro102761 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d269086 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d269172 q = 1) (hb : d332607 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d269172, d332607, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d269172, d332607, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
  have h11 (q : Pattern) (ha : d269199 q = 1) (hb : d332634 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d269199, d332634, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro102767 q ha hb
    | true =>
      simp only [d269199, d332634, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d269200 q = 1) (hb : d332635 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d269200, d332635, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d269200, d332635, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d269201 q = 1) (hb : d332636 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d269201, d332636, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d269201, d332636, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d269202 q = 1) (hb : d332637 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d269202, d332637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d269202, d332637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d269203 q = 1) (hb : d332638 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d269203, d332638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d269203, d332638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d269204 q = 1) (hb : d332639 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d269204, d332639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d269204, d332639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  exact h16 p ha hb
theorem andIntro102769 (p : Pattern) (ha : d269205 p = 1) (hb : d332640 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d269072 q = 1) (hb : d332526 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d269072, d332526, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro102741 q ha hb
    | true =>
      simp only [d269072, d332526, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d269073 q = 1) (hb : d332527 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d269073, d332527, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d269073, d332527, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d269076 q = 1) (hb : d332530 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d269076, d332530, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro102742 q ha hb
    | true =>
      simp only [d269076, d332530, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d269077 q = 1) (hb : d332531 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d269077, d332531, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d269077, d332531, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d269078 q = 1) (hb : d332532 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d269078, d332532, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d269078, d332532, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d269079 q = 1) (hb : d332533 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d269079, d332533, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d269079, d332533, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d269105 q = 1) (hb : d332559 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d269105, d332559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d269105, d332559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d269205 q = 1) (hb : d332640 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d269205, d332640, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d269205, d332640, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro102770 (p : Pattern) (ha : d269206 p = 1) (hb : d332641 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d269076 q = 1) (hb : d332530 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d269076, d332530, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro102742 q ha hb
    | true =>
      simp only [d269076, d332530, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d269077 q = 1) (hb : d332531 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d269077, d332531, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d269077, d332531, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d269082 q = 1) (hb : d332536 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d269082, d332536, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d269082, d332536, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d269083 q = 1) (hb : d332537 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d269083, d332537, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d269083, d332537, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d269107 q = 1) (hb : d332561 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d269107, d332561, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d269107, d332561, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d269206 q = 1) (hb : d332641 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d269206, d332641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d269206, d332641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro102771 (p : Pattern) (ha : d269211 p = 1) (hb : d332646 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d269072 q = 1) (hb : d332526 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d269072, d332526, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro102741 q ha hb
    | true =>
      simp only [d269072, d332526, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d269073 q = 1) (hb : d332527 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d269073, d332527, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d269073, d332527, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d269076 q = 1) (hb : d332530 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d269076, d332530, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro102742 q ha hb
    | true =>
      simp only [d269076, d332530, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d269077 q = 1) (hb : d332531 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d269077, d332531, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d269077, d332531, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d269078 q = 1) (hb : d332532 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d269078, d332532, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d269078, d332532, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d269113 q = 1) (hb : d332567 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d269113, d332567, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d269113, d332567, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d269114 q = 1) (hb : d332568 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d269114, d332568, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d269114, d332568, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d269211 q = 1) (hb : d332646 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d269211, d332646, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d269211, d332646, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro102772 (p : Pattern) (ha : d269212 p = 1) (hb : d332647 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d269076 q = 1) (hb : d332530 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d269076, d332530, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro102742 q ha hb
    | true =>
      simp only [d269076, d332530, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d269077 q = 1) (hb : d332531 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d269077, d332531, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d269077, d332531, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d269082 q = 1) (hb : d332536 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d269082, d332536, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d269082, d332536, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d269116 q = 1) (hb : d332570 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d269116, d332570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d269116, d332570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d269117 q = 1) (hb : d332571 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d269117, d332571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d269117, d332571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d269212 q = 1) (hb : d332647 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d269212, d332647, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d269212, d332647, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro102773 (p : Pattern) (ha : d269216 p = 1) (hb : d332651 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d269156 q = 1) (hb : d332600 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d269156, d332600, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro102758 q ha hb
    | true =>
      simp only [d269156, d332600, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d269157 q = 1) (hb : d332601 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d269157, d332601, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d269157, d332601, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d269161 q = 1) (hb : d332526 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d269161, d332526, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro102759 q ha hb
    | true =>
      simp only [d269161, d332526, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d269162 q = 1) (hb : d332527 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d269162, d332527, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d269162, d332527, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d269163 q = 1) (hb : d332602 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d269163, d332602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d269163, d332602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d269164 q = 1) (hb : d332603 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d269164, d332603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d269164, d332603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d269165 q = 1) (hb : d332604 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d269165, d332604, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d269165, d332604, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d269216 q = 1) (hb : d332651 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d269216, d332651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d269216, d332651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro102774 (p : Pattern) (ha : d269217 p = 1) (hb : d332548 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d269161 q = 1) (hb : d332526 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d269161, d332526, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro102759 q ha hb
    | true =>
      simp only [d269161, d332526, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d269162 q = 1) (hb : d332527 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d269162, d332527, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d269162, d332527, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d269076 q = 1) (hb : d332530 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d269076, d332530, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro102742 q ha hb
    | true =>
      simp only [d269076, d332530, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d269077 q = 1) (hb : d332531 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d269077, d332531, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d269077, d332531, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d269167 q = 1) (hb : d332532 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d269167, d332532, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d269167, d332532, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d269168 q = 1) (hb : d332533 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d269168, d332533, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d269168, d332533, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d269169 q = 1) (hb : d332534 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d269169, d332534, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d269169, d332534, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d269217 q = 1) (hb : d332548 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d269217, d332548, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d269217, d332548, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro102775 (p : Pattern) (ha : d269220 p = 1) (hb : d332654 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d269193 q = 1) (hb : d332628 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d269193, d332628, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro102766 q ha hb
    | true =>
      simp only [d269193, d332628, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d269194 q = 1) (hb : d332629 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d269194, d332629, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d269194, d332629, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d269195 q = 1) (hb : d332630 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d269195, d332630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d269195, d332630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d269196 q = 1) (hb : d332631 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d269196, d332631, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d269196, d332631, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d269197 q = 1) (hb : d332632 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d269197, d332632, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d269197, d332632, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d269220 q = 1) (hb : d332654 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d269220, d332654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d269220, d332654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro102776 (p : Pattern) (ha : d269226 p = 1) (hb : d332660 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d269109 q = 1) (hb : d332563 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d269109, d332563, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro102749 q ha hb
    | true =>
      simp only [d269109, d332563, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro102750 q ha hb
  have h2 (q : Pattern) (ha : d269110 q = 1) (hb : d332564 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d269110, d332564, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d269110, d332564, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d269111 q = 1) (hb : d332565 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d269111, d332565, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d269111, d332565, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d269112 q = 1) (hb : d332566 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d269112, d332566, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d269112, d332566, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d269119 q = 1) (hb : d332573 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d269119, d332573, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro102751 q ha hb
    | true =>
      simp only [d269119, d332573, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro102752 q ha hb
  have h6 (q : Pattern) (ha : d269120 q = 1) (hb : d332574 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d269120, d332574, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d269120, d332574, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d269121 q = 1) (hb : d332575 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d269121, d332575, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d269121, d332575, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d269171 q = 1) (hb : d332606 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d269171, d332606, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro102760 q ha hb
    | true =>
      simp only [d269171, d332606, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro102761 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d269086 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d269172 q = 1) (hb : d332607 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d269172, d332607, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d269172, d332607, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
  have h11 (q : Pattern) (ha : d269199 q = 1) (hb : d332634 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d269199, d332634, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro102767 q ha hb
    | true =>
      simp only [d269199, d332634, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d269200 q = 1) (hb : d332635 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d269200, d332635, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d269200, d332635, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d269201 q = 1) (hb : d332636 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d269201, d332636, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d269201, d332636, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d269202 q = 1) (hb : d332637 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d269202, d332637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d269202, d332637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d269203 q = 1) (hb : d332638 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d269203, d332638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d269203, d332638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d269207 q = 1) (hb : d332642 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d269207, d332642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro102769 q ha hb
    | true =>
      simp only [d269207, d332642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro102770 q ha hb
  have h17 (q : Pattern) (ha : d269208 q = 1) (hb : d332643 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d269208, d332643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d269208, d332643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d269209 q = 1) (hb : d332644 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d269209, d332644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d269209, d332644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h19 (q : Pattern) (ha : d269210 q = 1) (hb : d332645 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d269210, d332645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d269210, d332645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d269213 q = 1) (hb : d332648 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d269213, d332648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro102771 q ha hb
    | true =>
      simp only [d269213, d332648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro102772 q ha hb
  have h21 (q : Pattern) (ha : d269214 q = 1) (hb : d332649 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d269214, d332649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d269214, d332649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
  have h22 (q : Pattern) (ha : d269215 q = 1) (hb : d332650 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d269215, d332650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d269215, d332650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h23 (q : Pattern) (ha : d269218 q = 1) (hb : d332652 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d269218, d332652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro102773 q ha hb
    | true =>
      simp only [d269218, d332652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro102774 q ha hb
  have h24 (q : Pattern) (ha : d0 q = 1) (hb : d269096 q = 1) : d0 q = 1 := by
    exact ha
  have h25 (q : Pattern) (ha : d269219 q = 1) (hb : d332653 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d269219, d332653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
    | true =>
      simp only [d269219, d332653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q hb ha
  have h26 (q : Pattern) (ha : d269221 q = 1) (hb : d332655 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d269221, d332655, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro102775 q ha hb
    | true =>
      simp only [d269221, d332655, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h27 (q : Pattern) (ha : d269222 q = 1) (hb : d332656 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d269222, d332656, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h26 q ha hb
    | true =>
      simp only [d269222, d332656, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h28 (q : Pattern) (ha : d269223 q = 1) (hb : d332657 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d269223, d332657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q ha hb
    | true =>
      simp only [d269223, d332657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h27 q ha hb
  have h29 (q : Pattern) (ha : d269224 q = 1) (hb : d332658 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d269224, d332658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
    | true =>
      simp only [d269224, d332658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h28 q ha hb
  have h30 (q : Pattern) (ha : d269225 q = 1) (hb : d332659 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d269225, d332659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d269225, d332659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h29 q ha hb
  have h31 (q : Pattern) (ha : d269226 q = 1) (hb : d332660 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d269226, d332660, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d269226, d332660, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h30 q ha hb
  exact h31 p ha hb
theorem andIntro102777 (p : Pattern) (ha : d269238 p = 1) (hb : d332667 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d269228 q = 1) (hb : d332540 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d269228, d332540, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro102761 q ha hb
    | true =>
      simp only [d269228, d332540, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro102744 q ha hb
  have h2 (q : Pattern) (ha : d269229 q = 1) (hb : d332541 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d269229, d332541, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d269229, d332541, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d269230 q = 1) (hb : d332542 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d269230, d332542, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d269230, d332542, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d269231 q = 1) (hb : d332543 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d269231, d332543, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d269231, d332543, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d269232 q = 1) (hb : d332544 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d269232, d332544, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d269232, d332544, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d269233 q = 1) (hb : d332662 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d269233, d332662, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro102744 q ha hb
    | true =>
      simp only [d269233, d332662, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d269234 q = 1) (hb : d332663 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d269234, d332663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d269234, d332663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d269235 q = 1) (hb : d332664 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d269235, d332664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d269235, d332664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d269236 q = 1) (hb : d332665 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d269236, d332665, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d269236, d332665, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d269237 q = 1) (hb : d332666 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d269237, d332666, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d269237, d332666, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d269238 q = 1) (hb : d332667 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d269238, d332667, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d269238, d332667, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro102778 (p : Pattern) (ha : d269244 p = 1) (hb : d332673 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d269233 q = 1) (hb : d332662 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d269233, d332662, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro102744 q ha hb
    | true =>
      simp only [d269233, d332662, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d269234 q = 1) (hb : d332663 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d269234, d332663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d269234, d332663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d269235 q = 1) (hb : d332664 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d269235, d332664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d269235, d332664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d269236 q = 1) (hb : d332665 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d269236, d332665, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d269236, d332665, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d269237 q = 1) (hb : d332666 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d269237, d332666, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d269237, d332666, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d269239 q = 1) (hb : d332668 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d269239, d332668, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro102747 q ha hb
    | true =>
      simp only [d269239, d332668, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d269240 q = 1) (hb : d332669 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d269240, d332669, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d269240, d332669, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d269241 q = 1) (hb : d332670 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d269241, d332670, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d269241, d332670, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d269242 q = 1) (hb : d332671 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d269242, d332671, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d269242, d332671, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d269243 q = 1) (hb : d332672 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d269243, d332672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d269243, d332672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d269244 q = 1) (hb : d332673 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d269244, d332673, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d269244, d332673, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro102779 (p : Pattern) (ha : d269251 p = 1) (hb : d332680 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d269218 q = 1) (hb : d332652 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d269218, d332652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro102773 q ha hb
    | true =>
      simp only [d269218, d332652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro102774 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d269096 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d269219 q = 1) (hb : d332653 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d269219, d332653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d269219, d332653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d269221 q = 1) (hb : d332655 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d269221, d332655, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro102775 q ha hb
    | true =>
      simp only [d269221, d332655, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d269222 q = 1) (hb : d332656 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d269222, d332656, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d269222, d332656, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d269223 q = 1) (hb : d332657 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d269223, d332657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d269223, d332657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d269249 q = 1) (hb : d332678 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d269249, d332678, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d269249, d332678, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d269250 q = 1) (hb : d332679 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d269250, d332679, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d269250, d332679, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d269251 q = 1) (hb : d332680 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d269251, d332680, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d269251, d332680, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro102780 (p : Pattern) (ha : d269253 p = 1) (hb : d332682 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d269239 q = 1) (hb : d332668 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d269239, d332668, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro102747 q ha hb
    | true =>
      simp only [d269239, d332668, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d269240 q = 1) (hb : d332669 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d269240, d332669, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d269240, d332669, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d269241 q = 1) (hb : d332670 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d269241, d332670, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d269241, d332670, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d269242 q = 1) (hb : d332671 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d269242, d332671, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d269242, d332671, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d269243 q = 1) (hb : d332672 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d269243, d332672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d269243, d332672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d269253 q = 1) (hb : d332682 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d269253, d332682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d269253, d332682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro102781 (p : Pattern) (ha : d269273 p = 1) (hb : d332698 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d269259 q = 1) (hb : d312184 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d269259, d312184, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d269259, d312184, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro102753 q ha hb
  have h2 (q : Pattern) (ha : d269125 q = 1) (hb : d312058 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d269125, d312058, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro102753 q ha hb
    | true =>
      simp only [d269125, d312058, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d269260 q = 1) (hb : d312185 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d269260, d312185, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d269260, d312185, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d269126 q = 1) (hb : d312059 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d269126, d312059, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d269126, d312059, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d269261 q = 1) (hb : d312186 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d269261, d312186, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d269261, d312186, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d269262 q = 1) (hb : d312187 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d269262, d312187, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d269262, d312187, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d269263 q = 1) (hb : d332688 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d269263, d332688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d269263, d332688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro102754 q ha hb
  have h8 (q : Pattern) (ha : d269130 q = 1) (hb : d332577 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d269130, d332577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro102754 q ha hb
    | true =>
      simp only [d269130, d332577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d269264 q = 1) (hb : d332689 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d269264, d332689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d269264, d332689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d269131 q = 1) (hb : d332578 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d269131, d332578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d269131, d332578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h11 (q : Pattern) (ha : d269265 q = 1) (hb : d332690 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d269265, d332690, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d269265, d332690, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d269266 q = 1) (hb : d332691 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d269266, d332691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d269266, d332691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d269267 q = 1) (hb : d332692 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d269267, d332692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d269267, d332692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d269268 q = 1) (hb : d332693 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d269268, d332693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d269268, d332693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro102732 q ha hb
  have h15 (q : Pattern) (ha : d268997 q = 1) (hb : d332479 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d268997, d332479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro102732 q ha hb
    | true =>
      simp only [d268997, d332479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h16 (q : Pattern) (ha : d269269 q = 1) (hb : d332694 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d269269, d332694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d269269, d332694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d268998 q = 1) (hb : d332480 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d268998, d332480, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d268998, d332480, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h18 (q : Pattern) (ha : d269270 q = 1) (hb : d332695 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d269270, d332695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d269270, d332695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d269271 q = 1) (hb : d332696 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d269271, d332696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d269271, d332696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h20 (q : Pattern) (ha : d269272 q = 1) (hb : d332697 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d269272, d332697, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d269272, d332697, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
  have h21 (q : Pattern) (ha : d269273 q = 1) (hb : d332698 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d269273, d332698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d269273, d332698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
  exact h21 p ha hb
theorem andIntro102782 (p : Pattern) (ha : d269288 p = 1) (hb : d332713 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d269274 q = 1) (hb : d332699 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d269274, d332699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d269274, d332699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro102729 q ha hb
  have h2 (q : Pattern) (ha : d268979 q = 1) (hb : d332465 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d268979, d332465, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro102729 q ha hb
    | true =>
      simp only [d268979, d332465, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d269275 q = 1) (hb : d332700 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d269275, d332700, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d269275, d332700, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d268980 q = 1) (hb : d332466 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d268980, d332466, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d268980, d332466, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d269276 q = 1) (hb : d332701 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d269276, d332701, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d269276, d332701, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d269277 q = 1) (hb : d332702 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d269277, d332702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d269277, d332702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d269278 q = 1) (hb : d332703 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d269278, d332703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d269278, d332703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro102731 q ha hb
  have h8 (q : Pattern) (ha : d268988 q = 1) (hb : d332473 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d268988, d332473, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro102731 q ha hb
    | true =>
      simp only [d268988, d332473, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d269279 q = 1) (hb : d332704 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d269279, d332704, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d269279, d332704, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d268989 q = 1) (hb : d332474 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d268989, d332474, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d268989, d332474, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h11 (q : Pattern) (ha : d269280 q = 1) (hb : d332705 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d269280, d332705, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d269280, d332705, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d269281 q = 1) (hb : d332706 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d269281, d332706, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d269281, d332706, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d269282 q = 1) (hb : d332707 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d269282, d332707, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d269282, d332707, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d269268 q = 1) (hb : d332693 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d269268, d332693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d269268, d332693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro102732 q ha hb
  have h15 (q : Pattern) (ha : d268997 q = 1) (hb : d332479 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d268997, d332479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro102732 q ha hb
    | true =>
      simp only [d268997, d332479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h16 (q : Pattern) (ha : d269269 q = 1) (hb : d332694 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d269269, d332694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d269269, d332694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d268998 q = 1) (hb : d332480 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d268998, d332480, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d268998, d332480, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h18 (q : Pattern) (ha : d269270 q = 1) (hb : d332695 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d269270, d332695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d269270, d332695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d269271 q = 1) (hb : d332696 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d269271, d332696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d269271, d332696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h20 (q : Pattern) (ha : d269283 q = 1) (hb : d332708 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d269283, d332708, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d269283, d332708, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro102733 q ha hb
  have h21 (q : Pattern) (ha : d269013 q = 1) (hb : d332489 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d269013, d332489, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro102733 q ha hb
    | true =>
      simp only [d269013, d332489, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h22 (q : Pattern) (ha : d269284 q = 1) (hb : d332709 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d269284, d332709, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d269284, d332709, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
  have h23 (q : Pattern) (ha : d269014 q = 1) (hb : d332490 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d269014, d332490, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d269014, d332490, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h24 (q : Pattern) (ha : d269285 q = 1) (hb : d332710 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d269285, d332710, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
    | true =>
      simp only [d269285, d332710, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
  have h25 (q : Pattern) (ha : d269286 q = 1) (hb : d332711 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d269286, d332711, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q ha hb
    | true =>
      simp only [d269286, d332711, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h26 (q : Pattern) (ha : d269287 q = 1) (hb : d332712 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d269287, d332712, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d269287, d332712, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q ha hb
  have h27 (q : Pattern) (ha : d269288 q = 1) (hb : d332713 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d269288, d332713, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d269288, d332713, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h26 q ha hb
  exact h27 p ha hb
theorem andIntro102783 (p : Pattern) (ha : d269298 p = 1) (hb : d332723 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d269292 q = 1) (hb : d332717 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d269292, d332717, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d269292, d332717, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro102756 q ha hb
  have h2 (q : Pattern) (ha : d269144 q = 1) (hb : d332588 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d269144, d332588, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro102756 q ha hb
    | true =>
      simp only [d269144, d332588, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d269293 q = 1) (hb : d332718 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d269293, d332718, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d269293, d332718, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d269145 q = 1) (hb : d332589 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d269145, d332589, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d269145, d332589, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d269294 q = 1) (hb : d332719 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d269294, d332719, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d269294, d332719, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d269295 q = 1) (hb : d332720 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d269295, d332720, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d269295, d332720, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d269283 q = 1) (hb : d332708 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d269283, d332708, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d269283, d332708, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro102733 q ha hb
  have h8 (q : Pattern) (ha : d269013 q = 1) (hb : d332489 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d269013, d332489, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro102733 q ha hb
    | true =>
      simp only [d269013, d332489, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d269284 q = 1) (hb : d332709 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d269284, d332709, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d269284, d332709, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d269014 q = 1) (hb : d332490 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d269014, d332490, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d269014, d332490, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h11 (q : Pattern) (ha : d269285 q = 1) (hb : d332710 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d269285, d332710, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d269285, d332710, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d269286 q = 1) (hb : d332711 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d269286, d332711, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d269286, d332711, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d269296 q = 1) (hb : d332721 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d269296, d332721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d269296, d332721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d269297 q = 1) (hb : d332722 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d269297, d332722, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d269297, d332722, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h15 (q : Pattern) (ha : d269298 q = 1) (hb : d332723 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d269298, d332723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d269298, d332723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro102784 (p : Pattern) (ha : d269312 p = 1) (hb : d332737 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d269303 q = 1) (hb : d332728 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d269303, d332728, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d269303, d332728, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro102735 q ha hb
  have h2 (q : Pattern) (ha : d269026 q = 1) (hb : d332502 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d269026, d332502, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro102735 q ha hb
    | true =>
      simp only [d269026, d332502, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d269304 q = 1) (hb : d332729 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d269304, d332729, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d269304, d332729, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d269027 q = 1) (hb : d332503 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d269027, d332503, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d269027, d332503, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d269305 q = 1) (hb : d332730 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d269305, d332730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d269305, d332730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d269306 q = 1) (hb : d332731 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d269306, d332731, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d269306, d332731, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d269307 q = 1) (hb : d332732 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d269307, d332732, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d269307, d332732, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro102736 q ha hb
  have h8 (q : Pattern) (ha : d269031 q = 1) (hb : d332507 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d269031, d332507, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro102736 q ha hb
    | true =>
      simp only [d269031, d332507, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d269308 q = 1) (hb : d332733 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d269308, d332733, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d269308, d332733, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d269032 q = 1) (hb : d332508 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d269032, d332508, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d269032, d332508, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h11 (q : Pattern) (ha : d269309 q = 1) (hb : d332734 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d269309, d332734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d269309, d332734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d269310 q = 1) (hb : d332735 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d269310, d332735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d269310, d332735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d269311 q = 1) (hb : d332736 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d269311, d332736, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d269311, d332736, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d269283 q = 1) (hb : d332708 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d269283, d332708, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d269283, d332708, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro102733 q ha hb
  have h15 (q : Pattern) (ha : d269013 q = 1) (hb : d332489 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d269013, d332489, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro102733 q ha hb
    | true =>
      simp only [d269013, d332489, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h16 (q : Pattern) (ha : d269284 q = 1) (hb : d332709 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d269284, d332709, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d269284, d332709, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d269014 q = 1) (hb : d332490 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d269014, d332490, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d269014, d332490, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h18 (q : Pattern) (ha : d269285 q = 1) (hb : d332710 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d269285, d332710, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d269285, d332710, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d269286 q = 1) (hb : d332711 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d269286, d332711, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d269286, d332711, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h20 (q : Pattern) (ha : d269297 q = 1) (hb : d332722 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d269297, d332722, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d269297, d332722, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h21 (q : Pattern) (ha : d269312 q = 1) (hb : d332737 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d269312, d332737, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d269312, d332737, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
  exact h21 p ha hb
theorem andIntro102785 (p : Pattern) (ha : d269326 p = 1) (hb : d332742 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d269316 q = 1) (hb : d332732 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d269316, d332732, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d269316, d332732, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro102738 q ha hb
  have h2 (q : Pattern) (ha : d269045 q = 1) (hb : d332507 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d269045, d332507, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro102738 q ha hb
    | true =>
      simp only [d269045, d332507, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d269317 q = 1) (hb : d332733 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d269317, d332733, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d269317, d332733, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d269046 q = 1) (hb : d332508 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d269046, d332508, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d269046, d332508, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d269318 q = 1) (hb : d332734 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d269318, d332734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d269318, d332734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d269319 q = 1) (hb : d332735 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d269319, d332735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d269319, d332735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d269320 q = 1) (hb : d332741 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d269320, d332741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d269320, d332741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d37988 q = 1) (hb : d269321 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d37988, d269321, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d37988, d269321, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro82268 q ha hb
  have h9 (q : Pattern) (ha : d37590 q = 1) (hb : d269054 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d37590, d269054, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro82268 q ha hb
    | true =>
      simp only [d37590, d269054, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d37989 q = 1) (hb : d269322 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d37989, d269322, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d37989, d269322, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d37591 q = 1) (hb : d269055 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d37591, d269055, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d37591, d269055, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d37990 q = 1) (hb : d269323 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d37990, d269323, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d37990, d269323, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d37991 q = 1) (hb : d269324 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d37991, d269324, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d37991, d269324, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d37992 q = 1) (hb : d269325 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d37992, d269325, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d37992, d269325, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d269326 q = 1) (hb : d332742 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d269326, d332742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d269326, d332742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  exact h15 p ha hb
theorem andIntro102786 (p : Pattern) (ha : d269332 p = 1) (hb : d332748 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d269289 q = 1) (hb : d332714 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d269289, d332714, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro102781 q ha hb
    | true =>
      simp only [d269289, d332714, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro102782 q ha hb
  have h2 (q : Pattern) (ha : d269290 q = 1) (hb : d332715 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d269290, d332715, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d269290, d332715, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d269291 q = 1) (hb : d332716 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d269291, d332716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d269291, d332716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d269299 q = 1) (hb : d332724 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d269299, d332724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro102782 q ha hb
    | true =>
      simp only [d269299, d332724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro102783 q ha hb
  have h5 (q : Pattern) (ha : d269300 q = 1) (hb : d332725 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d269300, d332725, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d269300, d332725, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d269301 q = 1) (hb : d332726 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d269301, d332726, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d269301, d332726, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d269302 q = 1) (hb : d332727 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d269302, d332727, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d269302, d332727, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d269313 q = 1) (hb : d332738 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d269313, d332738, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro102782 q ha hb
    | true =>
      simp only [d269313, d332738, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro102784 q ha hb
  have h9 (q : Pattern) (ha : d269314 q = 1) (hb : d332739 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d269314, d332739, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d269314, d332739, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d269315 q = 1) (hb : d332740 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d269315, d332740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d269315, d332740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d269327 q = 1) (hb : d332743 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d269327, d332743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro102784 q ha hb
    | true =>
      simp only [d269327, d332743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro102785 q ha hb
  have h12 (q : Pattern) (ha : d269328 q = 1) (hb : d332744 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d269328, d332744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d269328, d332744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d269329 q = 1) (hb : d332745 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d269329, d332745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d269329, d332745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d269330 q = 1) (hb : d332746 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d269330, d332746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d269330, d332746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d269331 q = 1) (hb : d332747 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d269331, d332747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d269331, d332747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d269332 q = 1) (hb : d332748 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d269332, d332748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d269332, d332748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h16 p ha hb
theorem andIntro102787 (p : Pattern) (ha : d269337 p = 1) (hb : d332753 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d269313 q = 1) (hb : d332738 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d269313, d332738, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro102782 q ha hb
    | true =>
      simp only [d269313, d332738, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro102784 q ha hb
  have h2 (q : Pattern) (ha : d269314 q = 1) (hb : d332739 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d269314, d332739, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d269314, d332739, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d269315 q = 1) (hb : d332740 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d269315, d332740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d269315, d332740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d269327 q = 1) (hb : d332743 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d269327, d332743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro102784 q ha hb
    | true =>
      simp only [d269327, d332743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro102785 q ha hb
  have h5 (q : Pattern) (ha : d269328 q = 1) (hb : d332744 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d269328, d332744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d269328, d332744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d269329 q = 1) (hb : d332745 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d269329, d332745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d269329, d332745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d269330 q = 1) (hb : d332746 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d269330, d332746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d269330, d332746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d269335 q = 1) (hb : d332751 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d269335, d332751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d269335, d332751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d269336 q = 1) (hb : d332752 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d269336, d332752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d269336, d332752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d269337 q = 1) (hb : d332753 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d269337, d332753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d269337, d332753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h10 p ha hb
theorem andIntro102788 (p : Pattern) (ha : d269343 p = 1) (hb : d332759 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d269333 q = 1) (hb : d332749 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d269333, d332749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro102786 q ha hb
    | true =>
      simp only [d269333, d332749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d269334 q = 1) (hb : d332750 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d269334, d332750, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d269334, d332750, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d269338 q = 1) (hb : d332754 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d269338, d332754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro102787 q ha hb
    | true =>
      simp only [d269338, d332754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d269339 q = 1) (hb : d332755 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d269339, d332755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d269339, d332755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d269340 q = 1) (hb : d332756 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d269340, d332756, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d269340, d332756, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d269341 q = 1) (hb : d332757 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d269341, d332757, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d269341, d332757, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d269342 q = 1) (hb : d332758 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d269342, d332758, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d269342, d332758, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d269343 q = 1) (hb : d332759 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d269343, d332759, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d269343, d332759, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro102789 (p : Pattern) (ha : d269345 p = 1) (hb : d332742 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d269307 q = 1) (hb : d332732 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d269307, d332732, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d269307, d332732, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro102736 q ha hb
  have h2 (q : Pattern) (ha : d269031 q = 1) (hb : d332507 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d269031, d332507, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro102736 q ha hb
    | true =>
      simp only [d269031, d332507, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d269308 q = 1) (hb : d332733 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d269308, d332733, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d269308, d332733, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d269032 q = 1) (hb : d332508 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d269032, d332508, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d269032, d332508, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d269309 q = 1) (hb : d332734 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d269309, d332734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d269309, d332734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d269310 q = 1) (hb : d332735 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d269310, d332735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d269310, d332735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d269344 q = 1) (hb : d332741 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d269344, d332741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d269344, d332741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d37988 q = 1) (hb : d269321 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d37988, d269321, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d37988, d269321, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro82268 q ha hb
  have h9 (q : Pattern) (ha : d37590 q = 1) (hb : d269054 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d37590, d269054, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro82268 q ha hb
    | true =>
      simp only [d37590, d269054, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d37989 q = 1) (hb : d269322 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d37989, d269322, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d37989, d269322, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d37591 q = 1) (hb : d269055 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d37591, d269055, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d37591, d269055, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d37990 q = 1) (hb : d269323 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d37990, d269323, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d37990, d269323, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d37991 q = 1) (hb : d269324 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d37991, d269324, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d37991, d269324, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d37992 q = 1) (hb : d269325 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d37992, d269325, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d37992, d269325, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d269345 q = 1) (hb : d332742 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d269345, d332742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d269345, d332742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  exact h15 p ha hb
theorem andIntro102790 (p : Pattern) (ha : d269351 p = 1) (hb : d332761 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d269346 q = 1) (hb : d332743 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d269346, d332743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro102784 q ha hb
    | true =>
      simp only [d269346, d332743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro102789 q ha hb
  have h2 (q : Pattern) (ha : d269347 q = 1) (hb : d332744 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d269347, d332744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d269347, d332744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d269348 q = 1) (hb : d332745 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d269348, d332745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d269348, d332745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d269349 q = 1) (hb : d332751 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d269349, d332751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d269349, d332751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d269350 q = 1) (hb : d332760 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d269350, d332760, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d269350, d332760, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d269351 q = 1) (hb : d332761 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d269351, d332761, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d269351, d332761, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro102791 (p : Pattern) (ha : d269357 p = 1) (hb : d332767 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d269338 q = 1) (hb : d332754 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d269338, d332754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro102787 q ha hb
    | true =>
      simp only [d269338, d332754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d269339 q = 1) (hb : d332755 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d269339, d332755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d269339, d332755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d269352 q = 1) (hb : d332762 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d269352, d332762, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro102790 q ha hb
    | true =>
      simp only [d269352, d332762, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d269353 q = 1) (hb : d332763 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d269353, d332763, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d269353, d332763, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d269354 q = 1) (hb : d332764 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d269354, d332764, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d269354, d332764, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d269355 q = 1) (hb : d332765 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d269355, d332765, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d269355, d332765, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d269356 q = 1) (hb : d332766 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d269356, d332766, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d269356, d332766, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d269357 q = 1) (hb : d332767 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d269357, d332767, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d269357, d332767, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro102792 (p : Pattern) (ha : d269378 p = 1) (hb : d332775 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d269303 q = 1) (hb : d332728 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d269303, d332728, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d269303, d332728, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro102735 q ha hb
  have h2 (q : Pattern) (ha : d269026 q = 1) (hb : d332502 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d269026, d332502, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro102735 q ha hb
    | true =>
      simp only [d269026, d332502, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d269304 q = 1) (hb : d332729 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d269304, d332729, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d269304, d332729, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d269027 q = 1) (hb : d332503 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d269027, d332503, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d269027, d332503, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d269305 q = 1) (hb : d332730 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d269305, d332730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d269305, d332730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d269306 q = 1) (hb : d332731 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d269306, d332731, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d269306, d332731, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d269307 q = 1) (hb : d332732 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d269307, d332732, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d269307, d332732, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro102736 q ha hb
  have h8 (q : Pattern) (ha : d269031 q = 1) (hb : d332507 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d269031, d332507, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro102736 q ha hb
    | true =>
      simp only [d269031, d332507, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d269308 q = 1) (hb : d332733 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d269308, d332733, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d269308, d332733, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d269032 q = 1) (hb : d332508 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d269032, d332508, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d269032, d332508, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h11 (q : Pattern) (ha : d269309 q = 1) (hb : d332734 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d269309, d332734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d269309, d332734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d269310 q = 1) (hb : d332735 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d269310, d332735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d269310, d332735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d269311 q = 1) (hb : d332736 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d269311, d332736, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d269311, d332736, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d269373 q = 1) (hb : d332770 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d269373, d332770, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d269373, d332770, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro102762 q ha hb
  have h15 (q : Pattern) (ha : d269174 q = 1) (hb : d332609 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d269174, d332609, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro102762 q ha hb
    | true =>
      simp only [d269174, d332609, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h16 (q : Pattern) (ha : d269374 q = 1) (hb : d332771 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d269374, d332771, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d269374, d332771, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d269175 q = 1) (hb : d332610 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d269175, d332610, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d269175, d332610, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h18 (q : Pattern) (ha : d269375 q = 1) (hb : d332772 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d269375, d332772, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d269375, d332772, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d269376 q = 1) (hb : d332773 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d269376, d332773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d269376, d332773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h20 (q : Pattern) (ha : d269377 q = 1) (hb : d332774 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d269377, d332774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d269377, d332774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h21 (q : Pattern) (ha : d269378 q = 1) (hb : d332775 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d269378, d332775, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d269378, d332775, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
  exact h21 p ha hb
theorem andIntro102793 (p : Pattern) (ha : d269384 p = 1) (hb : d332781 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d269379 q = 1) (hb : d332776 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d269379, d332776, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d269379, d332776, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro102764 q ha hb
  have h2 (q : Pattern) (ha : d269181 q = 1) (hb : d332616 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d269181, d332616, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro102764 q ha hb
    | true =>
      simp only [d269181, d332616, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d269380 q = 1) (hb : d332777 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d269380, d332777, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d269380, d332777, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d269182 q = 1) (hb : d332617 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d269182, d332617, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d269182, d332617, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d269381 q = 1) (hb : d332778 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d269381, d332778, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d269381, d332778, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d269382 q = 1) (hb : d332779 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d269382, d332779, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d269382, d332779, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d269383 q = 1) (hb : d332780 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d269383, d332780, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d269383, d332780, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d269384 q = 1) (hb : d332781 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d269384, d332781, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d269384, d332781, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro102794 (p : Pattern) (ha : d269390 p = 1) (hb : d332787 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d269313 q = 1) (hb : d332738 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d269313, d332738, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro102782 q ha hb
    | true =>
      simp only [d269313, d332738, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro102784 q ha hb
  have h2 (q : Pattern) (ha : d269314 q = 1) (hb : d332739 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d269314, d332739, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d269314, d332739, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d269315 q = 1) (hb : d332740 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d269315, d332740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d269315, d332740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d269327 q = 1) (hb : d332743 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d269327, d332743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro102784 q ha hb
    | true =>
      simp only [d269327, d332743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro102785 q ha hb
  have h5 (q : Pattern) (ha : d269328 q = 1) (hb : d332744 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d269328, d332744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d269328, d332744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d269329 q = 1) (hb : d332745 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d269329, d332745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d269329, d332745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d269330 q = 1) (hb : d332746 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d269330, d332746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d269330, d332746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d269385 q = 1) (hb : d332782 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d269385, d332782, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro102792 q ha hb
    | true =>
      simp only [d269385, d332782, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro102793 q ha hb
  have h9 (q : Pattern) (ha : d269386 q = 1) (hb : d332783 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d269386, d332783, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d269386, d332783, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d269387 q = 1) (hb : d332784 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d269387, d332784, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d269387, d332784, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d269388 q = 1) (hb : d332785 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d269388, d332785, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d269388, d332785, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d269389 q = 1) (hb : d332786 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d269389, d332786, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d269389, d332786, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d269390 q = 1) (hb : d332787 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d269390, d332787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d269390, d332787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h13 p ha hb
theorem andIntro102795 (p : Pattern) (ha : d269396 p = 1) (hb : d332793 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d269391 q = 1) (hb : d332788 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d269391, d332788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro102794 q ha hb
    | true =>
      simp only [d269391, d332788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d269392 q = 1) (hb : d332789 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d269392, d332789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d269392, d332789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d269393 q = 1) (hb : d332790 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d269393, d332790, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d269393, d332790, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d269394 q = 1) (hb : d332791 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d269394, d332791, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d269394, d332791, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d269395 q = 1) (hb : d332792 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d269395, d332792, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d269395, d332792, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d269396 q = 1) (hb : d332793 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d269396, d332793, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d269396, d332793, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro102796 (p : Pattern) (ha : d269402 p = 1) (hb : d332799 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d269358 q = 1) (hb : d332768 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d269358, d332768, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro102788 q ha hb
    | true =>
      simp only [d269358, d332768, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro102791 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d269371 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d269372 q = 1) (hb : d332769 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d269372, d332769, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d269372, d332769, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d269397 q = 1) (hb : d332794 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d269397, d332794, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro102795 q ha hb
    | true =>
      simp only [d269397, d332794, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d269398 q = 1) (hb : d332795 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d269398, d332795, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d269398, d332795, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d269399 q = 1) (hb : d332796 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d269399, d332796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d269399, d332796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d269400 q = 1) (hb : d332797 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d269400, d332797, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d269400, d332797, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d269401 q = 1) (hb : d332798 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d269401, d332798, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d269401, d332798, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d269402 q = 1) (hb : d332799 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d269402, d332799, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d269402, d332799, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro102797 (p : Pattern) (ha : d269370 p = 1) (hb : d332804 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d269352 q = 1) (hb : d332762 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d269352, d332762, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro102790 q ha hb
    | true =>
      simp only [d269352, d332762, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d269353 q = 1) (hb : d332763 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d269353, d332763, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d269353, d332763, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d269367 q = 1) (hb : d332801 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d269367, d332801, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d269367, d332801, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d269368 q = 1) (hb : d332802 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d269368, d332802, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d269368, d332802, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d269369 q = 1) (hb : d332803 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d269369, d332803, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d269369, d332803, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d269370 q = 1) (hb : d332804 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d269370, d332804, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d269370, d332804, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro102798 (p : Pattern) (ha : d269409 p = 1) (hb : d332810 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d269404 q = 1) (hb : d332805 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d269404, d332805, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro102797 q ha hb
    | true =>
      simp only [d269404, d332805, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d269405 q = 1) (hb : d332806 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d269405, d332806, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d269405, d332806, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d269406 q = 1) (hb : d332807 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d269406, d332807, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d269406, d332807, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d269407 q = 1) (hb : d332808 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d269407, d332808, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d269407, d332808, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d269408 q = 1) (hb : d332809 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d269408, d332809, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d269408, d332809, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d269409 q = 1) (hb : d332810 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d269409, d332810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d269409, d332810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro102799 (p : Pattern) (ha : d269415 p = 1) (hb : d332816 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d269092 q = 1) (hb : d332546 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d269092, d332546, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d269092, d332546, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro102745 q ha hb
  have h2 (q : Pattern) (ha : d269093 q = 1) (hb : d332547 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d269093, d332547, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d269093, d332547, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d269102 q = 1) (hb : d332556 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d269102, d332556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro102745 q ha hb
    | true =>
      simp only [d269102, d332556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro102748 q ha hb
  have h4 (q : Pattern) (ha : d269103 q = 1) (hb : d332557 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d269103, d332557, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d269103, d332557, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d269104 q = 1) (hb : d332558 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d269104, d332558, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d269104, d332558, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d269227 q = 1) (hb : d332661 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d269227, d332661, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro102768 q ha hb
    | true =>
      simp only [d269227, d332661, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro102776 q ha hb
  have h7 (q : Pattern) (ha : d269245 q = 1) (hb : d332674 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d269245, d332674, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro102777 q ha hb
    | true =>
      simp only [d269245, d332674, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro102778 q ha hb
  have h8 (q : Pattern) (ha : d269246 q = 1) (hb : d332675 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d269246, d332675, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d269246, d332675, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d269247 q = 1) (hb : d332676 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d269247, d332676, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d269247, d332676, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h10 (q : Pattern) (ha : d269248 q = 1) (hb : d332677 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d269248, d332677, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d269248, d332677, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d269252 q = 1) (hb : d332681 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d269252, d332681, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d269252, d332681, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro102779 q ha hb
  have h12 (q : Pattern) (ha : d269254 q = 1) (hb : d332683 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d269254, d332683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d269254, d332683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro102780 q ha hb
  have h13 (q : Pattern) (ha : d269255 q = 1) (hb : d332684 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d269255, d332684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d269255, d332684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d269256 q = 1) (hb : d332685 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d269256, d332685, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d269256, d332685, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h15 (q : Pattern) (ha : d269257 q = 1) (hb : d332686 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d269257, d332686, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d269257, d332686, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h16 (q : Pattern) (ha : d269258 q = 1) (hb : d332687 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d269258, d332687, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d269258, d332687, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d269403 q = 1) (hb : d332800 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d269403, d332800, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d269403, d332800, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro102796 q ha hb
  have h18 (q : Pattern) (ha : d269410 q = 1) (hb : d332811 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d269410, d332811, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d269410, d332811, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro102798 q ha hb
  have h19 (q : Pattern) (ha : d269411 q = 1) (hb : d332812 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d269411, d332812, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d269411, d332812, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d269412 q = 1) (hb : d332813 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d269412, d332813, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d269412, d332813, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h21 (q : Pattern) (ha : d269413 q = 1) (hb : d332814 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d269413, d332814, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d269413, d332814, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h22 (q : Pattern) (ha : d269414 q = 1) (hb : d332815 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d269414, d332815, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d269414, d332815, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h23 (q : Pattern) (ha : d269415 q = 1) (hb : d332816 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d269415, d332816, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d269415, d332816, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
  exact h23 p ha hb
theorem andIntro102800 (p : Pattern) (ha : d269421 p = 1) (hb : d332822 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d269416 q = 1) (hb : d332817 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d269416, d332817, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d269416, d332817, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro102799 q ha hb
  have h2 (q : Pattern) (ha : d269417 q = 1) (hb : d332818 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d269417, d332818, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d269417, d332818, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d269418 q = 1) (hb : d332819 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d269418, d332819, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d269418, d332819, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d269419 q = 1) (hb : d332820 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d269419, d332820, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d269419, d332820, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d269420 q = 1) (hb : d332821 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d269420, d332821, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d269420, d332821, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d269421 q = 1) (hb : d332822 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d269421, d332822, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d269421, d332822, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro102801 (p : Pattern) (ha : d38177 p = 1) (hb : d269442 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d269432 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d10055 q = 1) (hb : d101482 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d10055, d101482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d10055, d101482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23340 q ha hb
  have h3 (q : Pattern) (ha : d38167 q = 1) (hb : d269438 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d38167, d269438, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d38167, d269438, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d38168 q = 1) (hb : d269439 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d38168, d269439, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d38168, d269439, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h5 (q : Pattern) (ha : d38169 q = 1) (hb : d269440 q = 1) : d0 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d38169, d269440, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d38169, d269440, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h6 (q : Pattern) (ha : d38170 q = 1) (hb : d269441 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d38170, d269441, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d38170, d269441, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h7 (q : Pattern) (ha : d38177 q = 1) (hb : d269442 q = 1) : d0 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d38177, d269442, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d38177, d269442, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro102802 (p : Pattern) (ha : d269463 p = 1) (hb : d332833 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d269428 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d10055 q = 1) (hb : d101482 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d10055, d101482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d10055, d101482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23340 q ha hb
  have h3 (q : Pattern) (ha : d38167 q = 1) (hb : d269453 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d38167, d269453, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d38167, d269453, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d38168 q = 1) (hb : d269454 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d38168, d269454, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d38168, d269454, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h5 (q : Pattern) (ha : d38169 q = 1) (hb : d269455 q = 1) : d0 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d38169, d269455, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d38169, d269455, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h6 (q : Pattern) (ha : d38170 q = 1) (hb : d269456 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d38170, d269456, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d38170, d269456, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h7 (q : Pattern) (ha : d0 q = 1) (hb : d69322 q = 1) : d0 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d5128 q = 1) (hb : d53322 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d5128, d53322, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d5128, d53322, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro99135 q ha hb
  have h9 (q : Pattern) (ha : d269457 q = 1) (hb : d332827 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d269457, d332827, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
    | true =>
      simp only [d269457, d332827, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d53327 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d269458 q = 1) (hb : d332828 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d269458, d332828, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d269458, d332828, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d53326 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d1564 q = 1) (hb : d101727 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d1564, d101727, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro99135 q ha hb
    | true =>
      simp only [d1564, d101727, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h14 (q : Pattern) (ha : d269459 q = 1) (hb : d332829 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d269459, d332829, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
    | true =>
      simp only [d269459, d332829, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q hb ha
  have h15 (q : Pattern) (ha : d269460 q = 1) (hb : d332830 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d269460, d332830, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d269460, d332830, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h16 (q : Pattern) (ha : d269461 q = 1) (hb : d332831 q = 1) : d0 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d269461, d332831, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d269461, d332831, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d269462 q = 1) (hb : d332832 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d269462, d332832, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d269462, d332832, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h18 (q : Pattern) (ha : d269463 q = 1) (hb : d332833 q = 1) : d0 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d269463, d332833, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
    | true =>
      simp only [d269463, d332833, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro102803 (p : Pattern) (ha : d269469 p = 1) (hb : d332839 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d269437 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d38178 q = 1) (hb : d269443 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d38178, d269443, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro102801 q ha hb
    | true =>
      simp only [d38178, d269443, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d38179 q = 1) (hb : d269444 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d38179, d269444, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d38179, d269444, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h4 (q : Pattern) (ha : d38180 q = 1) (hb : d269445 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d38180, d269445, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d38180, d269445, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d38181 q = 1) (hb : d269446 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d38181, d269446, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d38181, d269446, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h6 (q : Pattern) (ha : d38302 q = 1) (hb : d269447 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d38302, d269447, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d38302, d269447, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d38178 q = 1) (hb : d269449 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d38178, d269449, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro82333 q ha hb
    | true =>
      simp only [d38178, d269449, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h8 (q : Pattern) (ha : d38179 q = 1) (hb : d269450 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d38179, d269450, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d38179, d269450, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h9 (q : Pattern) (ha : d38180 q = 1) (hb : d269451 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d38180, d269451, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d38180, d269451, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d38181 q = 1) (hb : d269452 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d38181, d269452, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d38181, d269452, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h11 (q : Pattern) (ha : d269464 q = 1) (hb : d332834 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d269464, d332834, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro102802 q ha hb
    | true =>
      simp only [d269464, d332834, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h12 (q : Pattern) (ha : d269465 q = 1) (hb : d332835 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d269465, d332835, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d269465, d332835, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h13 (q : Pattern) (ha : d269466 q = 1) (hb : d332836 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d269466, d332836, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d269466, d332836, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d269467 q = 1) (hb : d332837 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d269467, d332837, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d269467, d332837, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h15 (q : Pattern) (ha : d269468 q = 1) (hb : d332838 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d269468, d332838, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
    | true =>
      simp only [d269468, d332838, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d269469 q = 1) (hb : d332839 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d269469, d332839, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
    | true =>
      simp only [d269469, d332839, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  exact h16 p ha hb
theorem andIntro102804 (p : Pattern) (ha : d38177 p = 1) (hb : d269476 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d269432 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d269428 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d10055 q = 1) (hb : d101482 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d10055, d101482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d10055, d101482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23340 q ha hb
  have h4 (q : Pattern) (ha : d38167 q = 1) (hb : d269453 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d38167, d269453, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d38167, d269453, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d269472 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d38168 q = 1) (hb : d269473 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d38168, d269473, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d38168, d269473, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d0 q = 1) (hb : d53328 q = 1) : d0 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d38169 q = 1) (hb : d269474 q = 1) : d0 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d38169, d269474, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d38169, d269474, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d38170 q = 1) (hb : d269475 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d38170, d269475, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d38170, d269475, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h10 (q : Pattern) (ha : d38177 q = 1) (hb : d269476 q = 1) : d0 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d38177, d269476, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d38177, d269476, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro102805 (p : Pattern) (ha : d269481 p = 1) (hb : d332833 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d269428 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d10055 q = 1) (hb : d101482 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d10055, d101482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d10055, d101482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23340 q ha hb
  have h3 (q : Pattern) (ha : d38167 q = 1) (hb : d269453 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d38167, d269453, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d38167, d269453, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d269472 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d38168 q = 1) (hb : d269473 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d38168, d269473, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d38168, d269473, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d53328 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d38169 q = 1) (hb : d269474 q = 1) : d0 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d38169, d269474, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d38169, d269474, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d38170 q = 1) (hb : d269475 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d38170, d269475, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d38170, d269475, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d69322 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d5128 q = 1) (hb : d53322 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d5128, d53322, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d5128, d53322, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro99135 q ha hb
  have h11 (q : Pattern) (ha : d269457 q = 1) (hb : d332827 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d269457, d332827, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
    | true =>
      simp only [d269457, d332827, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d53327 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d269458 q = 1) (hb : d332828 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d269458, d332828, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d269458, d332828, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d53326 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d1564 q = 1) (hb : d101727 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d1564, d101727, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro99135 q ha hb
    | true =>
      simp only [d1564, d101727, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h16 (q : Pattern) (ha : d269459 q = 1) (hb : d332829 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d269459, d332829, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
    | true =>
      simp only [d269459, d332829, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q hb ha
  have h17 (q : Pattern) (ha : d269460 q = 1) (hb : d332830 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d269460, d332830, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d269460, d332830, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h18 (q : Pattern) (ha : d269461 q = 1) (hb : d332831 q = 1) : d0 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d269461, d332831, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d269461, d332831, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d269462 q = 1) (hb : d332832 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d269462, d332832, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d269462, d332832, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h20 (q : Pattern) (ha : d269481 q = 1) (hb : d332833 q = 1) : d0 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d269481, d332833, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
    | true =>
      simp only [d269481, d332833, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
  exact h20 p ha hb
theorem andIntro102806 (p : Pattern) (ha : d269488 p = 1) (hb : d332841 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d38178 q = 1) (hb : d269477 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d38178, d269477, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro102804 q ha hb
    | true =>
      simp only [d38178, d269477, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d38179 q = 1) (hb : d269478 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d38179, d269478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d38179, d269478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d38180 q = 1) (hb : d269479 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d38180, d269479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d38180, d269479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d38181 q = 1) (hb : d269480 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d38181, d269480, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d38181, d269480, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d269482 q = 1) (hb : d332834 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d269482, d332834, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro102805 q ha hb
    | true =>
      simp only [d269482, d332834, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d269483 q = 1) (hb : d332835 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d269483, d332835, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d269483, d332835, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d269484 q = 1) (hb : d332836 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d269484, d332836, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d269484, d332836, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d269485 q = 1) (hb : d332837 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d269485, d332837, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d269485, d332837, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d269486 q = 1) (hb : d332838 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d269486, d332838, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d269486, d332838, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d269464 q = 1) (hb : d332834 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d269464, d332834, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro102802 q ha hb
    | true =>
      simp only [d269464, d332834, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h11 (q : Pattern) (ha : d269465 q = 1) (hb : d332835 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d269465, d332835, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d269465, d332835, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d269466 q = 1) (hb : d332836 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d269466, d332836, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d269466, d332836, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d269467 q = 1) (hb : d332837 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d269467, d332837, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d269467, d332837, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h14 (q : Pattern) (ha : d269487 q = 1) (hb : d332840 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d269487, d332840, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d269487, d332840, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h15 (q : Pattern) (ha : d269488 q = 1) (hb : d332841 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d269488, d332841, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d269488, d332841, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro102807 (p : Pattern) (ha : d269495 p = 1) (hb : d332833 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d269428 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d10055 q = 1) (hb : d101482 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d10055, d101482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d10055, d101482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23340 q ha hb
  have h3 (q : Pattern) (ha : d38167 q = 1) (hb : d269453 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d38167, d269453, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d38167, d269453, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d69323 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d38168 q = 1) (hb : d269492 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d38168, d269492, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d38168, d269492, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d53328 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d38169 q = 1) (hb : d269493 q = 1) : d0 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d38169, d269493, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d38169, d269493, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d38170 q = 1) (hb : d269494 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d38170, d269494, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d38170, d269494, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d69322 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d5128 q = 1) (hb : d53322 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d5128, d53322, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d5128, d53322, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro99135 q ha hb
  have h11 (q : Pattern) (ha : d269457 q = 1) (hb : d332827 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d269457, d332827, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
    | true =>
      simp only [d269457, d332827, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d53327 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d269458 q = 1) (hb : d332828 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d269458, d332828, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d269458, d332828, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d53326 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d1564 q = 1) (hb : d101727 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d1564, d101727, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro99135 q ha hb
    | true =>
      simp only [d1564, d101727, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h16 (q : Pattern) (ha : d269459 q = 1) (hb : d332829 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d269459, d332829, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
    | true =>
      simp only [d269459, d332829, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q hb ha
  have h17 (q : Pattern) (ha : d269460 q = 1) (hb : d332830 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d269460, d332830, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d269460, d332830, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h18 (q : Pattern) (ha : d269461 q = 1) (hb : d332831 q = 1) : d0 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d269461, d332831, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d269461, d332831, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d269462 q = 1) (hb : d332832 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d269462, d332832, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d269462, d332832, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h20 (q : Pattern) (ha : d269495 q = 1) (hb : d332833 q = 1) : d0 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d269495, d332833, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
    | true =>
      simp only [d269495, d332833, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
  exact h20 p ha hb
theorem andIntro102808 (p : Pattern) (ha : d269504 p = 1) (hb : d332845 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d69322 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d5128 q = 1) (hb : d53322 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d5128, d53322, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d5128, d53322, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro99135 q ha hb
  have h3 (q : Pattern) (ha : d269457 q = 1) (hb : d332827 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d269457, d332827, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d269457, d332827, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d269501 q = 1) (hb : d332828 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d269501, d332828, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d269501, d332828, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d53326 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d1564 q = 1) (hb : d101727 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d1564, d101727, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro99135 q ha hb
    | true =>
      simp only [d1564, d101727, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h7 (q : Pattern) (ha : d269459 q = 1) (hb : d332829 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d269459, d332829, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
    | true =>
      simp only [d269459, d332829, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d269460 q = 1) (hb : d332830 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d269460, d332830, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d269460, d332830, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h9 (q : Pattern) (ha : d269502 q = 1) (hb : d332831 q = 1) : d0 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d269502, d332831, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d269502, d332831, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d269503 q = 1) (hb : d332832 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d269503, d332832, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d269503, d332832, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h11 (q : Pattern) (ha : d269504 q = 1) (hb : d332845 q = 1) : d0 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d269504, d332845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d269504, d332845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  exact h11 p ha hb
theorem andIntro102809 (p : Pattern) (ha : d269510 p = 1) (hb : d332851 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d269496 q = 1) (hb : d332834 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d269496, d332834, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro102807 q ha hb
    | true =>
      simp only [d269496, d332834, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d269497 q = 1) (hb : d332835 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d269497, d332835, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d269497, d332835, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d269498 q = 1) (hb : d332836 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d269498, d332836, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d269498, d332836, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d269499 q = 1) (hb : d332837 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d269499, d332837, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d269499, d332837, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d269500 q = 1) (hb : d332840 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d269500, d332840, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d269500, d332840, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d269505 q = 1) (hb : d332846 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d269505, d332846, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro102808 q ha hb
    | true =>
      simp only [d269505, d332846, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d269506 q = 1) (hb : d332847 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d269506, d332847, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d269506, d332847, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d269507 q = 1) (hb : d332848 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d269507, d332848, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d269507, d332848, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d269508 q = 1) (hb : d332849 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d269508, d332849, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d269508, d332849, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h10 (q : Pattern) (ha : d269509 q = 1) (hb : d332850 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d269509, d332850, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d269509, d332850, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h11 (q : Pattern) (ha : d269510 q = 1) (hb : d332851 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d269510, d332851, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d269510, d332851, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro102810 (p : Pattern) (ha : d269516 p = 1) (hb : d332851 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d269482 q = 1) (hb : d332834 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d269482, d332834, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro102805 q ha hb
    | true =>
      simp only [d269482, d332834, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d269483 q = 1) (hb : d332835 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d269483, d332835, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d269483, d332835, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d269484 q = 1) (hb : d332836 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d269484, d332836, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d269484, d332836, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d269485 q = 1) (hb : d332837 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d269485, d332837, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d269485, d332837, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d269515 q = 1) (hb : d332840 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d269515, d332840, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d269515, d332840, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d269505 q = 1) (hb : d332846 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d269505, d332846, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro102808 q ha hb
    | true =>
      simp only [d269505, d332846, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d269506 q = 1) (hb : d332847 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d269506, d332847, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d269506, d332847, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d269507 q = 1) (hb : d332848 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d269507, d332848, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d269507, d332848, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d269508 q = 1) (hb : d332849 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d269508, d332849, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d269508, d332849, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h10 (q : Pattern) (ha : d269509 q = 1) (hb : d332850 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d269509, d332850, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d269509, d332850, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h11 (q : Pattern) (ha : d269516 q = 1) (hb : d332851 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d269516, d332851, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d269516, d332851, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro102811 (p : Pattern) (ha : d269522 p = 1) (hb : d332858 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d269489 q = 1) (hb : d332842 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d269489, d332842, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro102803 q ha hb
    | true =>
      simp only [d269489, d332842, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro102806 q ha hb
  have h2 (q : Pattern) (ha : d269490 q = 1) (hb : d332843 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d269490, d332843, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d269490, d332843, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d269491 q = 1) (hb : d332844 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d269491, d332844, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d269491, d332844, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d269511 q = 1) (hb : d332852 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d269511, d332852, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro102806 q ha hb
    | true =>
      simp only [d269511, d332852, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro102809 q ha hb
  have h5 (q : Pattern) (ha : d269512 q = 1) (hb : d332853 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d269512, d332853, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d269512, d332853, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d269513 q = 1) (hb : d332854 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d269513, d332854, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d269513, d332854, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d269514 q = 1) (hb : d332855 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d269514, d332855, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d269514, d332855, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d269517 q = 1) (hb : d332852 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d269517, d332852, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro102806 q ha hb
    | true =>
      simp only [d269517, d332852, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro102810 q ha hb
  have h9 (q : Pattern) (ha : d269518 q = 1) (hb : d332853 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d269518, d332853, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d269518, d332853, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d269519 q = 1) (hb : d332854 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d269519, d332854, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d269519, d332854, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d269520 q = 1) (hb : d332856 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d269520, d332856, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d269520, d332856, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d269521 q = 1) (hb : d332857 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d269521, d332857, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d269521, d332857, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d269522 q = 1) (hb : d332858 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d269522, d332858, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d269522, d332858, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h13 p ha hb
theorem andIntro102812 (p : Pattern) (ha : d269526 p = 1) (hb : d332862 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d269517 q = 1) (hb : d332852 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d269517, d332852, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro102806 q ha hb
    | true =>
      simp only [d269517, d332852, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro102810 q ha hb
  have h2 (q : Pattern) (ha : d269518 q = 1) (hb : d332853 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d269518, d332853, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d269518, d332853, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d269519 q = 1) (hb : d332854 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d269519, d332854, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d269519, d332854, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d269520 q = 1) (hb : d332856 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d269520, d332856, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d269520, d332856, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d269525 q = 1) (hb : d332861 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d269525, d332861, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d269525, d332861, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d269526 q = 1) (hb : d332862 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d269526, d332862, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d269526, d332862, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro102813 (p : Pattern) (ha : d269532 p = 1) (hb : d332868 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d269523 q = 1) (hb : d332859 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d269523, d332859, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro102811 q ha hb
    | true =>
      simp only [d269523, d332859, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d269524 q = 1) (hb : d332860 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d269524, d332860, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d269524, d332860, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d269527 q = 1) (hb : d332863 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d269527, d332863, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro102812 q ha hb
    | true =>
      simp only [d269527, d332863, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d269528 q = 1) (hb : d332864 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d269528, d332864, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d269528, d332864, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d269529 q = 1) (hb : d332865 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d269529, d332865, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d269529, d332865, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d269530 q = 1) (hb : d332866 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d269530, d332866, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d269530, d332866, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d269531 q = 1) (hb : d332867 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d269531, d332867, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d269531, d332867, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d269532 q = 1) (hb : d332868 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d269532, d332868, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d269532, d332868, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro102814 (p : Pattern) (ha : d269536 p = 1) (hb : d332872 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d269527 q = 1) (hb : d332863 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d269527, d332863, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro102812 q ha hb
    | true =>
      simp only [d269527, d332863, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d269528 q = 1) (hb : d332864 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d269528, d332864, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d269528, d332864, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d269533 q = 1) (hb : d332869 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d269533, d332869, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d269533, d332869, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d269534 q = 1) (hb : d332870 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d269534, d332870, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d269534, d332870, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d269535 q = 1) (hb : d332871 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d269535, d332871, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d269535, d332871, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d269536 q = 1) (hb : d332872 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d269536, d332872, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d269536, d332872, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro102815 (p : Pattern) (ha : d269542 p = 1) (hb : d332878 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d269537 q = 1) (hb : d332873 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d269537, d332873, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro102813 q ha hb
    | true =>
      simp only [d269537, d332873, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro102814 q ha hb
  have h2 (q : Pattern) (ha : d269538 q = 1) (hb : d332874 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d269538, d332874, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d269538, d332874, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d269539 q = 1) (hb : d332875 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d269539, d332875, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d269539, d332875, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d269540 q = 1) (hb : d332876 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d269540, d332876, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d269540, d332876, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d269541 q = 1) (hb : d332877 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d269541, d332877, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d269541, d332877, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d269542 q = 1) (hb : d332878 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d269542, d332878, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d269542, d332878, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro102816 (p : Pattern) (ha : d269545 p = 1) (hb : d332881 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d269523 q = 1) (hb : d332859 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d269523, d332859, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro102811 q ha hb
    | true =>
      simp only [d269523, d332859, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d269524 q = 1) (hb : d332860 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d269524, d332860, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d269524, d332860, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d269527 q = 1) (hb : d332863 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d269527, d332863, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro102812 q ha hb
    | true =>
      simp only [d269527, d332863, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d269528 q = 1) (hb : d332864 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d269528, d332864, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d269528, d332864, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d269529 q = 1) (hb : d332865 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d269529, d332865, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d269529, d332865, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d269530 q = 1) (hb : d332866 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d269530, d332866, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d269530, d332866, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d269531 q = 1) (hb : d332867 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d269531, d332867, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d269531, d332867, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d269545 q = 1) (hb : d332881 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d269545, d332881, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d269545, d332881, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro102817 (p : Pattern) (ha : d269546 p = 1) (hb : d332882 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d269527 q = 1) (hb : d332863 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d269527, d332863, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro102812 q ha hb
    | true =>
      simp only [d269527, d332863, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d269528 q = 1) (hb : d332864 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d269528, d332864, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d269528, d332864, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d269533 q = 1) (hb : d332869 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d269533, d332869, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d269533, d332869, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d269534 q = 1) (hb : d332870 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d269534, d332870, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d269534, d332870, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d269535 q = 1) (hb : d332871 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d269535, d332871, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d269535, d332871, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d269546 q = 1) (hb : d332882 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d269546, d332882, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d269546, d332882, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro102818 (p : Pattern) (ha : d269552 p = 1) (hb : d332888 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d269537 q = 1) (hb : d332873 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d269537, d332873, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro102813 q ha hb
    | true =>
      simp only [d269537, d332873, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro102814 q ha hb
  have h2 (q : Pattern) (ha : d269538 q = 1) (hb : d332874 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d269538, d332874, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d269538, d332874, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d269539 q = 1) (hb : d332875 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d269539, d332875, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d269539, d332875, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d269540 q = 1) (hb : d332876 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d269540, d332876, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d269540, d332876, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d269541 q = 1) (hb : d332877 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d269541, d332877, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d269541, d332877, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d269547 q = 1) (hb : d332883 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d269547, d332883, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro102816 q ha hb
    | true =>
      simp only [d269547, d332883, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro102817 q ha hb
  have h7 (q : Pattern) (ha : d269548 q = 1) (hb : d332884 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d269548, d332884, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d269548, d332884, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d269549 q = 1) (hb : d332885 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d269549, d332885, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d269549, d332885, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d269550 q = 1) (hb : d332886 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d269550, d332886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d269550, d332886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d269551 q = 1) (hb : d332887 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d269551, d332887, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d269551, d332887, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d269552 q = 1) (hb : d332888 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d269552, d332888, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d269552, d332888, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro102819 (p : Pattern) (ha : d269557 p = 1) (hb : d332893 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d269523 q = 1) (hb : d332859 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d269523, d332859, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro102811 q ha hb
    | true =>
      simp only [d269523, d332859, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d269524 q = 1) (hb : d332860 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d269524, d332860, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d269524, d332860, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d269527 q = 1) (hb : d332863 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d269527, d332863, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro102812 q ha hb
    | true =>
      simp only [d269527, d332863, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d269528 q = 1) (hb : d332864 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d269528, d332864, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d269528, d332864, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d269529 q = 1) (hb : d332865 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d269529, d332865, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d269529, d332865, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d269530 q = 1) (hb : d332866 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d269530, d332866, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d269530, d332866, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d269556 q = 1) (hb : d332892 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d269556, d332892, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d269556, d332892, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d269557 q = 1) (hb : d332893 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d269557, d332893, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d269557, d332893, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro102820 (p : Pattern) (ha : d269559 p = 1) (hb : d332895 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d269527 q = 1) (hb : d332863 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d269527, d332863, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro102812 q ha hb
    | true =>
      simp only [d269527, d332863, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d269528 q = 1) (hb : d332864 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d269528, d332864, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d269528, d332864, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d269533 q = 1) (hb : d332869 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d269533, d332869, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d269533, d332869, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d269534 q = 1) (hb : d332870 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d269534, d332870, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d269534, d332870, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d269558 q = 1) (hb : d332894 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d269558, d332894, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d269558, d332894, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d269559 q = 1) (hb : d332895 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d269559, d332895, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d269559, d332895, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro102821 (p : Pattern) (ha : d269566 p = 1) (hb : d332902 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d269523 q = 1) (hb : d332859 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d269523, d332859, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro102811 q ha hb
    | true =>
      simp only [d269523, d332859, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d269524 q = 1) (hb : d332860 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d269524, d332860, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d269524, d332860, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d269527 q = 1) (hb : d332863 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d269527, d332863, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro102812 q ha hb
    | true =>
      simp only [d269527, d332863, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d269528 q = 1) (hb : d332864 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d269528, d332864, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d269528, d332864, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d269529 q = 1) (hb : d332865 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d269529, d332865, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d269529, d332865, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d269564 q = 1) (hb : d332900 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d269564, d332900, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d269564, d332900, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d269565 q = 1) (hb : d332901 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d269565, d332901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d269565, d332901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d269566 q = 1) (hb : d332902 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d269566, d332902, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d269566, d332902, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro102822 (p : Pattern) (ha : d269569 p = 1) (hb : d332905 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d269527 q = 1) (hb : d332863 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d269527, d332863, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro102812 q ha hb
    | true =>
      simp only [d269527, d332863, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d269528 q = 1) (hb : d332864 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d269528, d332864, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d269528, d332864, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d269533 q = 1) (hb : d332869 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d269533, d332869, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d269533, d332869, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d269567 q = 1) (hb : d332903 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d269567, d332903, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d269567, d332903, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d269568 q = 1) (hb : d332904 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d269568, d332904, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d269568, d332904, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d269569 q = 1) (hb : d332905 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d269569, d332905, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d269569, d332905, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro102823 (p : Pattern) (ha : d269578 p = 1) (hb : d332841 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d38178 q = 1) (hb : d269449 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d38178, d269449, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro82333 q ha hb
    | true =>
      simp only [d38178, d269449, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d38179 q = 1) (hb : d269450 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d38179, d269450, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d38179, d269450, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d38180 q = 1) (hb : d269451 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d38180, d269451, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d38180, d269451, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d38181 q = 1) (hb : d269452 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d38181, d269452, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d38181, d269452, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d269464 q = 1) (hb : d332834 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d269464, d332834, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro102802 q ha hb
    | true =>
      simp only [d269464, d332834, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d269465 q = 1) (hb : d332835 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d269465, d332835, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d269465, d332835, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d269466 q = 1) (hb : d332836 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d269466, d332836, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d269466, d332836, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d269467 q = 1) (hb : d332837 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d269467, d332837, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d269467, d332837, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d269468 q = 1) (hb : d332838 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d269468, d332838, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d269468, d332838, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d269487 q = 1) (hb : d332840 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d269487, d332840, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d269487, d332840, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h11 (q : Pattern) (ha : d269578 q = 1) (hb : d332841 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d269578, d332841, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d269578, d332841, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro102824 (p : Pattern) (ha : d269584 p = 1) (hb : d332914 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d269575 q = 1) (hb : d332909 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d269575, d332909, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro82357 q hb ha
    | true =>
      simp only [d269575, d332909, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro102803 q ha hb
  have h2 (q : Pattern) (ha : d269576 q = 1) (hb : d332910 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d269576, d332910, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d269576, d332910, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d269577 q = 1) (hb : d332911 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d269577, d332911, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d269577, d332911, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d269579 q = 1) (hb : d332842 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d269579, d332842, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro102803 q ha hb
    | true =>
      simp only [d269579, d332842, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro102823 q ha hb
  have h5 (q : Pattern) (ha : d269580 q = 1) (hb : d332843 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d269580, d332843, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d269580, d332843, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d269581 q = 1) (hb : d332844 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d269581, d332844, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d269581, d332844, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d269582 q = 1) (hb : d332912 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d269582, d332912, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d269582, d332912, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d269489 q = 1) (hb : d332842 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d269489, d332842, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro102803 q ha hb
    | true =>
      simp only [d269489, d332842, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro102806 q ha hb
  have h9 (q : Pattern) (ha : d269490 q = 1) (hb : d332843 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d269490, d332843, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d269490, d332843, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d269491 q = 1) (hb : d332844 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d269491, d332844, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d269491, d332844, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d269511 q = 1) (hb : d332852 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d269511, d332852, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro102806 q ha hb
    | true =>
      simp only [d269511, d332852, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro102809 q ha hb
  have h12 (q : Pattern) (ha : d269512 q = 1) (hb : d332853 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d269512, d332853, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d269512, d332853, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d269513 q = 1) (hb : d332854 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d269513, d332854, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d269513, d332854, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d269514 q = 1) (hb : d332855 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d269514, d332855, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d269514, d332855, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d269583 q = 1) (hb : d332913 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d269583, d332913, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d269583, d332913, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d269584 q = 1) (hb : d332914 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d269584, d332914, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d269584, d332914, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h16 p ha hb
theorem andIntro102825 (p : Pattern) (ha : d269589 p = 1) (hb : d332858 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d269489 q = 1) (hb : d332842 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d269489, d332842, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro102803 q ha hb
    | true =>
      simp only [d269489, d332842, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro102806 q ha hb
  have h2 (q : Pattern) (ha : d269490 q = 1) (hb : d332843 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d269490, d332843, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d269490, d332843, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d269491 q = 1) (hb : d332844 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d269491, d332844, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d269491, d332844, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d269511 q = 1) (hb : d332852 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d269511, d332852, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro102806 q ha hb
    | true =>
      simp only [d269511, d332852, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro102809 q ha hb
  have h5 (q : Pattern) (ha : d269512 q = 1) (hb : d332853 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d269512, d332853, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d269512, d332853, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d269513 q = 1) (hb : d332854 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d269513, d332854, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d269513, d332854, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d269514 q = 1) (hb : d332855 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d269514, d332855, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d269514, d332855, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d269587 q = 1) (hb : d332856 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d269587, d332856, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d269587, d332856, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d269588 q = 1) (hb : d332857 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d269588, d332857, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d269588, d332857, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d269589 q = 1) (hb : d332858 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d269589, d332858, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d269589, d332858, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h10 p ha hb
theorem andIntro102826 (p : Pattern) (ha : d269595 p = 1) (hb : d332920 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d269585 q = 1) (hb : d332915 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d269585, d332915, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro102824 q ha hb
    | true =>
      simp only [d269585, d332915, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d269586 q = 1) (hb : d332916 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d269586, d332916, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d269586, d332916, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d269590 q = 1) (hb : d332859 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d269590, d332859, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro102825 q ha hb
    | true =>
      simp only [d269590, d332859, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d269591 q = 1) (hb : d332860 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d269591, d332860, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d269591, d332860, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d269592 q = 1) (hb : d332917 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d269592, d332917, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d269592, d332917, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d269593 q = 1) (hb : d332918 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d269593, d332918, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d269593, d332918, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d269594 q = 1) (hb : d332919 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d269594, d332919, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d269594, d332919, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d269595 q = 1) (hb : d332920 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d269595, d332920, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d269595, d332920, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro102827 (p : Pattern) (ha : d269599 p = 1) (hb : d332868 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d269590 q = 1) (hb : d332859 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d269590, d332859, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro102825 q ha hb
    | true =>
      simp only [d269590, d332859, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d269591 q = 1) (hb : d332860 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d269591, d332860, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d269591, d332860, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d269527 q = 1) (hb : d332863 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d269527, d332863, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro102812 q ha hb
    | true =>
      simp only [d269527, d332863, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d269528 q = 1) (hb : d332864 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d269528, d332864, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d269528, d332864, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d269596 q = 1) (hb : d332865 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d269596, d332865, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d269596, d332865, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d269597 q = 1) (hb : d332866 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d269597, d332866, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d269597, d332866, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d269598 q = 1) (hb : d332867 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d269598, d332867, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d269598, d332867, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d269599 q = 1) (hb : d332868 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d269599, d332868, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d269599, d332868, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro102828 (p : Pattern) (ha : d269602 p = 1) (hb : d324966 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d269428 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d10055 q = 1) (hb : d101482 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d10055, d101482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d10055, d101482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23340 q ha hb
  have h3 (q : Pattern) (ha : d38167 q = 1) (hb : d269453 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d38167, d269453, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d38167, d269453, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d38168 q = 1) (hb : d269454 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d38168, d269454, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d38168, d269454, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h5 (q : Pattern) (ha : d38169 q = 1) (hb : d269455 q = 1) : d0 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d38169, d269455, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d38169, d269455, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h6 (q : Pattern) (ha : d38170 q = 1) (hb : d269456 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d38170, d269456, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d38170, d269456, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h7 (q : Pattern) (ha : d0 q = 1) (hb : d69329 q = 1) : d0 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d269602 q = 1) (hb : d324966 q = 1) : d0 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d269602, d324966, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
    | true =>
      simp only [d269602, d324966, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
  exact h8 p ha hb
theorem andIntro102829 (p : Pattern) (ha : d269608 p = 1) (hb : d332923 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d38178 q = 1) (hb : d269477 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d38178, d269477, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro102804 q ha hb
    | true =>
      simp only [d38178, d269477, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d38179 q = 1) (hb : d269478 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d38179, d269478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d38179, d269478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d38180 q = 1) (hb : d269479 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d38180, d269479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d38180, d269479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d38181 q = 1) (hb : d269480 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d38181, d269480, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d38181, d269480, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d269482 q = 1) (hb : d332834 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d269482, d332834, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro102805 q ha hb
    | true =>
      simp only [d269482, d332834, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d269483 q = 1) (hb : d332835 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d269483, d332835, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d269483, d332835, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d269484 q = 1) (hb : d332836 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d269484, d332836, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d269484, d332836, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d269485 q = 1) (hb : d332837 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d269485, d332837, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d269485, d332837, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d269486 q = 1) (hb : d332838 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d269486, d332838, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d269486, d332838, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d269603 q = 1) (hb : d324967 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d269603, d324967, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro102828 q ha hb
    | true =>
      simp only [d269603, d324967, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h11 (q : Pattern) (ha : d269604 q = 1) (hb : d324968 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d269604, d324968, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d269604, d324968, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d269605 q = 1) (hb : d324969 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d269605, d324969, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d269605, d324969, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d269606 q = 1) (hb : d324970 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d269606, d324970, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d269606, d324970, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h14 (q : Pattern) (ha : d269607 q = 1) (hb : d324971 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d269607, d324971, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d269607, d324971, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h15 (q : Pattern) (ha : d269608 q = 1) (hb : d332923 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d269608, d332923, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d269608, d332923, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro102830 (p : Pattern) (ha : d269609 p = 1) (hb : d324966 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d269428 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d10055 q = 1) (hb : d101482 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d10055, d101482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d10055, d101482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23340 q ha hb
  have h3 (q : Pattern) (ha : d38167 q = 1) (hb : d269453 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d38167, d269453, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d38167, d269453, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d269472 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d38168 q = 1) (hb : d269473 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d38168, d269473, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d38168, d269473, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d53328 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d38169 q = 1) (hb : d269474 q = 1) : d0 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d38169, d269474, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d38169, d269474, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d38170 q = 1) (hb : d269475 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d38170, d269475, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d38170, d269475, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d69329 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d269609 q = 1) (hb : d324966 q = 1) : d0 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d269609, d324966, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
    | true =>
      simp only [d269609, d324966, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
  exact h10 p ha hb
theorem andIntro102831 (p : Pattern) (ha : d269615 p = 1) (hb : d324973 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d269610 q = 1) (hb : d324967 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d269610, d324967, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro102830 q ha hb
    | true =>
      simp only [d269610, d324967, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d269611 q = 1) (hb : d324968 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d269611, d324968, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d269611, d324968, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d269612 q = 1) (hb : d324969 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d269612, d324969, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d269612, d324969, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d269613 q = 1) (hb : d324970 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d269613, d324970, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d269613, d324970, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d269614 q = 1) (hb : d324971 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d269614, d324971, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d269614, d324971, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d269615 q = 1) (hb : d324973 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d269615, d324973, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d269615, d324973, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro102832 (p : Pattern) (ha : d269621 p = 1) (hb : d332929 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d269489 q = 1) (hb : d332842 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d269489, d332842, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro102803 q ha hb
    | true =>
      simp only [d269489, d332842, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro102806 q ha hb
  have h2 (q : Pattern) (ha : d269490 q = 1) (hb : d332843 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d269490, d332843, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d269490, d332843, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d269491 q = 1) (hb : d332844 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d269491, d332844, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d269491, d332844, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d269511 q = 1) (hb : d332852 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d269511, d332852, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro102806 q ha hb
    | true =>
      simp only [d269511, d332852, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro102809 q ha hb
  have h5 (q : Pattern) (ha : d269512 q = 1) (hb : d332853 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d269512, d332853, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d269512, d332853, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d269513 q = 1) (hb : d332854 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d269513, d332854, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d269513, d332854, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d269514 q = 1) (hb : d332855 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d269514, d332855, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d269514, d332855, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d269616 q = 1) (hb : d332924 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d269616, d332924, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro102829 q ha hb
    | true =>
      simp only [d269616, d332924, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro102831 q ha hb
  have h9 (q : Pattern) (ha : d269617 q = 1) (hb : d332925 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d269617, d332925, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d269617, d332925, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d269618 q = 1) (hb : d332926 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d269618, d332926, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d269618, d332926, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d269619 q = 1) (hb : d332927 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d269619, d332927, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d269619, d332927, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d269620 q = 1) (hb : d332928 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d269620, d332928, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d269620, d332928, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d269621 q = 1) (hb : d332929 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d269621, d332929, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d269621, d332929, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h13 p ha hb
theorem andIntro102833 (p : Pattern) (ha : d269627 p = 1) (hb : d332935 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d269622 q = 1) (hb : d332930 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d269622, d332930, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro102832 q ha hb
    | true =>
      simp only [d269622, d332930, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d269623 q = 1) (hb : d332931 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d269623, d332931, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d269623, d332931, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d269624 q = 1) (hb : d332932 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d269624, d332932, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d269624, d332932, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d269625 q = 1) (hb : d332933 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d269625, d332933, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d269625, d332933, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d269626 q = 1) (hb : d332934 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d269626, d332934, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d269626, d332934, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d269627 q = 1) (hb : d332935 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d269627, d332935, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d269627, d332935, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro102834 (p : Pattern) (ha : d269633 p = 1) (hb : d332941 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d269560 q = 1) (hb : d332896 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d269560, d332896, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro102819 q ha hb
    | true =>
      simp only [d269560, d332896, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro102820 q ha hb
  have h2 (q : Pattern) (ha : d269561 q = 1) (hb : d332897 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d269561, d332897, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d269561, d332897, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d269562 q = 1) (hb : d332898 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d269562, d332898, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d269562, d332898, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d269563 q = 1) (hb : d332899 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d269563, d332899, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d269563, d332899, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d269570 q = 1) (hb : d332906 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d269570, d332906, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro102821 q ha hb
    | true =>
      simp only [d269570, d332906, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro102822 q ha hb
  have h6 (q : Pattern) (ha : d269571 q = 1) (hb : d332907 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d269571, d332907, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d269571, d332907, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d269572 q = 1) (hb : d332908 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d269572, d332908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d269572, d332908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d269600 q = 1) (hb : d332921 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d269600, d332921, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro102826 q ha hb
    | true =>
      simp only [d269600, d332921, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro102827 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d269537 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d269601 q = 1) (hb : d332922 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d269601, d332922, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d269601, d332922, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
  have h11 (q : Pattern) (ha : d269628 q = 1) (hb : d332936 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d269628, d332936, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro102833 q ha hb
    | true =>
      simp only [d269628, d332936, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d269629 q = 1) (hb : d332937 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d269629, d332937, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d269629, d332937, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d269630 q = 1) (hb : d332938 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d269630, d332938, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d269630, d332938, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d269631 q = 1) (hb : d332939 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d269631, d332939, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d269631, d332939, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d269632 q = 1) (hb : d332940 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d269632, d332940, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d269632, d332940, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d269633 q = 1) (hb : d332941 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d269633, d332941, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d269633, d332941, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  exact h16 p ha hb
theorem andIntro102835 (p : Pattern) (ha : d269634 p = 1) (hb : d332942 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d269523 q = 1) (hb : d332859 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d269523, d332859, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro102811 q ha hb
    | true =>
      simp only [d269523, d332859, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d269524 q = 1) (hb : d332860 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d269524, d332860, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d269524, d332860, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d269527 q = 1) (hb : d332863 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d269527, d332863, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro102812 q ha hb
    | true =>
      simp only [d269527, d332863, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d269528 q = 1) (hb : d332864 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d269528, d332864, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d269528, d332864, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d269529 q = 1) (hb : d332865 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d269529, d332865, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d269529, d332865, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d269530 q = 1) (hb : d332866 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d269530, d332866, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d269530, d332866, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d269556 q = 1) (hb : d332892 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d269556, d332892, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d269556, d332892, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d269634 q = 1) (hb : d332942 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d269634, d332942, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d269634, d332942, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro102836 (p : Pattern) (ha : d269635 p = 1) (hb : d332943 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d269527 q = 1) (hb : d332863 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d269527, d332863, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro102812 q ha hb
    | true =>
      simp only [d269527, d332863, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d269528 q = 1) (hb : d332864 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d269528, d332864, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d269528, d332864, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d269533 q = 1) (hb : d332869 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d269533, d332869, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d269533, d332869, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d269534 q = 1) (hb : d332870 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d269534, d332870, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d269534, d332870, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d269558 q = 1) (hb : d332894 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d269558, d332894, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d269558, d332894, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d269635 q = 1) (hb : d332943 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d269635, d332943, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d269635, d332943, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro102837 (p : Pattern) (ha : d269640 p = 1) (hb : d332948 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d269523 q = 1) (hb : d332859 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d269523, d332859, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro102811 q ha hb
    | true =>
      simp only [d269523, d332859, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d269524 q = 1) (hb : d332860 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d269524, d332860, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d269524, d332860, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d269527 q = 1) (hb : d332863 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d269527, d332863, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro102812 q ha hb
    | true =>
      simp only [d269527, d332863, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d269528 q = 1) (hb : d332864 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d269528, d332864, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d269528, d332864, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d269529 q = 1) (hb : d332865 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d269529, d332865, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d269529, d332865, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d269564 q = 1) (hb : d332900 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d269564, d332900, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d269564, d332900, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d269565 q = 1) (hb : d332901 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d269565, d332901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d269565, d332901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d269640 q = 1) (hb : d332948 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d269640, d332948, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d269640, d332948, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro102838 (p : Pattern) (ha : d269641 p = 1) (hb : d332949 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d269527 q = 1) (hb : d332863 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d269527, d332863, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro102812 q ha hb
    | true =>
      simp only [d269527, d332863, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d269528 q = 1) (hb : d332864 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d269528, d332864, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d269528, d332864, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d269533 q = 1) (hb : d332869 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d269533, d332869, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d269533, d332869, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d269567 q = 1) (hb : d332903 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d269567, d332903, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d269567, d332903, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d269568 q = 1) (hb : d332904 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d269568, d332904, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d269568, d332904, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d269641 q = 1) (hb : d332949 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d269641, d332949, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d269641, d332949, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro102839 (p : Pattern) (ha : d269645 p = 1) (hb : d332953 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d269585 q = 1) (hb : d332915 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d269585, d332915, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro102824 q ha hb
    | true =>
      simp only [d269585, d332915, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d269586 q = 1) (hb : d332916 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d269586, d332916, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d269586, d332916, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d269590 q = 1) (hb : d332859 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d269590, d332859, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro102825 q ha hb
    | true =>
      simp only [d269590, d332859, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d269591 q = 1) (hb : d332860 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d269591, d332860, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d269591, d332860, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d269592 q = 1) (hb : d332917 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d269592, d332917, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d269592, d332917, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d269593 q = 1) (hb : d332918 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d269593, d332918, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d269593, d332918, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d269594 q = 1) (hb : d332919 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d269594, d332919, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d269594, d332919, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d269645 q = 1) (hb : d332953 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d269645, d332953, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d269645, d332953, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro102840 (p : Pattern) (ha : d269646 p = 1) (hb : d332881 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d269590 q = 1) (hb : d332859 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d269590, d332859, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro102825 q ha hb
    | true =>
      simp only [d269590, d332859, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d269591 q = 1) (hb : d332860 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d269591, d332860, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d269591, d332860, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d269527 q = 1) (hb : d332863 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d269527, d332863, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro102812 q ha hb
    | true =>
      simp only [d269527, d332863, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d269528 q = 1) (hb : d332864 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d269528, d332864, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d269528, d332864, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d269596 q = 1) (hb : d332865 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d269596, d332865, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d269596, d332865, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d269597 q = 1) (hb : d332866 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d269597, d332866, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d269597, d332866, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d269598 q = 1) (hb : d332867 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d269598, d332867, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d269598, d332867, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d269646 q = 1) (hb : d332881 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d269646, d332881, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d269646, d332881, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro102841 (p : Pattern) (ha : d269649 p = 1) (hb : d332956 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d269622 q = 1) (hb : d332930 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d269622, d332930, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro102832 q ha hb
    | true =>
      simp only [d269622, d332930, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d269623 q = 1) (hb : d332931 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d269623, d332931, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d269623, d332931, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d269624 q = 1) (hb : d332932 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d269624, d332932, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d269624, d332932, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d269625 q = 1) (hb : d332933 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d269625, d332933, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d269625, d332933, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d269626 q = 1) (hb : d332934 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d269626, d332934, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d269626, d332934, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d269649 q = 1) (hb : d332956 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d269649, d332956, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d269649, d332956, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro102842 (p : Pattern) (ha : d269655 p = 1) (hb : d332962 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d269560 q = 1) (hb : d332896 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d269560, d332896, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro102819 q ha hb
    | true =>
      simp only [d269560, d332896, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro102820 q ha hb
  have h2 (q : Pattern) (ha : d269561 q = 1) (hb : d332897 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d269561, d332897, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d269561, d332897, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d269562 q = 1) (hb : d332898 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d269562, d332898, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d269562, d332898, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d269563 q = 1) (hb : d332899 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d269563, d332899, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d269563, d332899, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d269570 q = 1) (hb : d332906 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d269570, d332906, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro102821 q ha hb
    | true =>
      simp only [d269570, d332906, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro102822 q ha hb
  have h6 (q : Pattern) (ha : d269571 q = 1) (hb : d332907 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d269571, d332907, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d269571, d332907, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d269572 q = 1) (hb : d332908 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d269572, d332908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d269572, d332908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d269600 q = 1) (hb : d332921 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d269600, d332921, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro102826 q ha hb
    | true =>
      simp only [d269600, d332921, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro102827 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d269537 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d269601 q = 1) (hb : d332922 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d269601, d332922, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d269601, d332922, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
  have h11 (q : Pattern) (ha : d269628 q = 1) (hb : d332936 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d269628, d332936, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro102833 q ha hb
    | true =>
      simp only [d269628, d332936, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d269629 q = 1) (hb : d332937 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d269629, d332937, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d269629, d332937, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d269630 q = 1) (hb : d332938 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d269630, d332938, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d269630, d332938, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d269631 q = 1) (hb : d332939 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d269631, d332939, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d269631, d332939, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d269632 q = 1) (hb : d332940 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d269632, d332940, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d269632, d332940, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d269636 q = 1) (hb : d332944 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d269636, d332944, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro102835 q ha hb
    | true =>
      simp only [d269636, d332944, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro102836 q ha hb
  have h17 (q : Pattern) (ha : d269637 q = 1) (hb : d332945 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d269637, d332945, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d269637, d332945, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d269638 q = 1) (hb : d332946 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d269638, d332946, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d269638, d332946, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h19 (q : Pattern) (ha : d269639 q = 1) (hb : d332947 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d269639, d332947, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d269639, d332947, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d269642 q = 1) (hb : d332950 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d269642, d332950, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro102837 q ha hb
    | true =>
      simp only [d269642, d332950, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro102838 q ha hb
  have h21 (q : Pattern) (ha : d269643 q = 1) (hb : d332951 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d269643, d332951, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d269643, d332951, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
  have h22 (q : Pattern) (ha : d269644 q = 1) (hb : d332952 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d269644, d332952, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d269644, d332952, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h23 (q : Pattern) (ha : d269647 q = 1) (hb : d332954 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d269647, d332954, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro102839 q ha hb
    | true =>
      simp only [d269647, d332954, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro102840 q ha hb
  have h24 (q : Pattern) (ha : d0 q = 1) (hb : d269547 q = 1) : d0 q = 1 := by
    exact ha
  have h25 (q : Pattern) (ha : d269648 q = 1) (hb : d332955 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d269648, d332955, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
    | true =>
      simp only [d269648, d332955, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q hb ha
  have h26 (q : Pattern) (ha : d269650 q = 1) (hb : d332957 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d269650, d332957, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro102841 q ha hb
    | true =>
      simp only [d269650, d332957, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h27 (q : Pattern) (ha : d269651 q = 1) (hb : d332958 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d269651, d332958, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h26 q ha hb
    | true =>
      simp only [d269651, d332958, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h28 (q : Pattern) (ha : d269652 q = 1) (hb : d332959 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d269652, d332959, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q ha hb
    | true =>
      simp only [d269652, d332959, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h27 q ha hb
  have h29 (q : Pattern) (ha : d269653 q = 1) (hb : d332960 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d269653, d332960, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
    | true =>
      simp only [d269653, d332960, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h28 q ha hb
  have h30 (q : Pattern) (ha : d269654 q = 1) (hb : d332961 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d269654, d332961, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d269654, d332961, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h29 q ha hb
  have h31 (q : Pattern) (ha : d269655 q = 1) (hb : d332962 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d269655, d332962, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d269655, d332962, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h30 q ha hb
  exact h31 p ha hb
theorem andIntro102843 (p : Pattern) (ha : d269667 p = 1) (hb : d332969 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d269657 q = 1) (hb : d332873 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d269657, d332873, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro102827 q ha hb
    | true =>
      simp only [d269657, d332873, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro102814 q ha hb
  have h2 (q : Pattern) (ha : d269658 q = 1) (hb : d332874 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d269658, d332874, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d269658, d332874, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d269659 q = 1) (hb : d332875 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d269659, d332875, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d269659, d332875, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d269660 q = 1) (hb : d332876 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d269660, d332876, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d269660, d332876, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d269661 q = 1) (hb : d332877 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d269661, d332877, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d269661, d332877, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d269662 q = 1) (hb : d332964 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d269662, d332964, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro102814 q ha hb
    | true =>
      simp only [d269662, d332964, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d269663 q = 1) (hb : d332965 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d269663, d332965, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d269663, d332965, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d269664 q = 1) (hb : d332966 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d269664, d332966, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d269664, d332966, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d269665 q = 1) (hb : d332967 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d269665, d332967, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d269665, d332967, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d269666 q = 1) (hb : d332968 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d269666, d332968, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d269666, d332968, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d269667 q = 1) (hb : d332969 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d269667, d332969, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d269667, d332969, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro102844 (p : Pattern) (ha : d269673 p = 1) (hb : d332975 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d269662 q = 1) (hb : d332964 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d269662, d332964, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro102814 q ha hb
    | true =>
      simp only [d269662, d332964, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d269663 q = 1) (hb : d332965 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d269663, d332965, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d269663, d332965, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d269664 q = 1) (hb : d332966 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d269664, d332966, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d269664, d332966, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d269665 q = 1) (hb : d332967 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d269665, d332967, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d269665, d332967, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d269666 q = 1) (hb : d332968 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d269666, d332968, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d269666, d332968, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d269668 q = 1) (hb : d332970 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d269668, d332970, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro102817 q ha hb
    | true =>
      simp only [d269668, d332970, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d269669 q = 1) (hb : d332971 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d269669, d332971, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d269669, d332971, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d269670 q = 1) (hb : d332972 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d269670, d332972, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d269670, d332972, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d269671 q = 1) (hb : d332973 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d269671, d332973, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d269671, d332973, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d269672 q = 1) (hb : d332974 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d269672, d332974, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d269672, d332974, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d269673 q = 1) (hb : d332975 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d269673, d332975, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d269673, d332975, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro102845 (p : Pattern) (ha : d269680 p = 1) (hb : d332982 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d269647 q = 1) (hb : d332954 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d269647, d332954, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro102839 q ha hb
    | true =>
      simp only [d269647, d332954, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro102840 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d269547 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d269648 q = 1) (hb : d332955 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d269648, d332955, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d269648, d332955, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d269650 q = 1) (hb : d332957 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d269650, d332957, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro102841 q ha hb
    | true =>
      simp only [d269650, d332957, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d269651 q = 1) (hb : d332958 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d269651, d332958, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d269651, d332958, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d269652 q = 1) (hb : d332959 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d269652, d332959, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d269652, d332959, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d269678 q = 1) (hb : d332980 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d269678, d332980, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d269678, d332980, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d269679 q = 1) (hb : d332981 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d269679, d332981, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d269679, d332981, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d269680 q = 1) (hb : d332982 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d269680, d332982, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d269680, d332982, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro102846 (p : Pattern) (ha : d269682 p = 1) (hb : d332984 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d269668 q = 1) (hb : d332970 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d269668, d332970, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro102817 q ha hb
    | true =>
      simp only [d269668, d332970, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d269669 q = 1) (hb : d332971 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d269669, d332971, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d269669, d332971, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d269670 q = 1) (hb : d332972 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d269670, d332972, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d269670, d332972, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d269671 q = 1) (hb : d332973 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d269671, d332973, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d269671, d332973, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d269672 q = 1) (hb : d332974 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d269672, d332974, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d269672, d332974, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d269682 q = 1) (hb : d332984 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d269682, d332984, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d269682, d332984, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro102847 (p : Pattern) (ha : d269708 p = 1) (hb : d332995 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d269697 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d38532 q = 1) (hb : d269698 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d38532, d269698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d38532, d269698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro102801 q ha hb
  have h3 (q : Pattern) (ha : d38178 q = 1) (hb : d269443 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d38178, d269443, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro102801 q ha hb
    | true =>
      simp only [d38178, d269443, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h4 (q : Pattern) (ha : d38533 q = 1) (hb : d269699 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d38533, d269699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d38533, d269699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d38179 q = 1) (hb : d269444 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d38179, d269444, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d38179, d269444, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h6 (q : Pattern) (ha : d38534 q = 1) (hb : d269700 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d38534, d269700, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d38534, d269700, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d38535 q = 1) (hb : d269701 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d38535, d269701, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d38535, d269701, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h8 (q : Pattern) (ha : d38536 q = 1) (hb : d269702 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d38536, d269702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d38536, d269702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d38532 q = 1) (hb : d269688 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d38532, d269688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d38532, d269688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro82333 q ha hb
  have h10 (q : Pattern) (ha : d38178 q = 1) (hb : d269449 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d38178, d269449, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro82333 q ha hb
    | true =>
      simp only [d38178, d269449, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h11 (q : Pattern) (ha : d38533 q = 1) (hb : d269689 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d38533, d269689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d38533, d269689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d38179 q = 1) (hb : d269450 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d38179, d269450, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d38179, d269450, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h13 (q : Pattern) (ha : d38534 q = 1) (hb : d269690 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d38534, d269690, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d38534, d269690, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d38535 q = 1) (hb : d269691 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d38535, d269691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d38535, d269691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h15 (q : Pattern) (ha : d269703 q = 1) (hb : d332990 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d269703, d332990, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d269703, d332990, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro102802 q ha hb
  have h16 (q : Pattern) (ha : d269464 q = 1) (hb : d332834 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d269464, d332834, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro102802 q ha hb
    | true =>
      simp only [d269464, d332834, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h17 (q : Pattern) (ha : d269704 q = 1) (hb : d332991 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d269704, d332991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d269704, d332991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d269465 q = 1) (hb : d332835 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d269465, d332835, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d269465, d332835, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h19 (q : Pattern) (ha : d269705 q = 1) (hb : d332992 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d269705, d332992, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d269705, d332992, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d269706 q = 1) (hb : d332993 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d269706, d332993, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d269706, d332993, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h21 (q : Pattern) (ha : d269707 q = 1) (hb : d332994 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d269707, d332994, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
    | true =>
      simp only [d269707, d332994, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
  have h22 (q : Pattern) (ha : d269708 q = 1) (hb : d332995 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d269708, d332995, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
    | true =>
      simp only [d269708, d332995, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
  exact h22 p ha hb
theorem andIntro102848 (p : Pattern) (ha : d269713 p = 1) (hb : d333000 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d38532 q = 1) (hb : d269688 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d38532, d269688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d38532, d269688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro82333 q ha hb
  have h2 (q : Pattern) (ha : d38178 q = 1) (hb : d269449 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d38178, d269449, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro82333 q ha hb
    | true =>
      simp only [d38178, d269449, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d38533 q = 1) (hb : d269689 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d38533, d269689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d38533, d269689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d38179 q = 1) (hb : d269450 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d38179, d269450, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d38179, d269450, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d38534 q = 1) (hb : d269690 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d38534, d269690, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d38534, d269690, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d38535 q = 1) (hb : d269691 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d38535, d269691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d38535, d269691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d269703 q = 1) (hb : d332990 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d269703, d332990, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d269703, d332990, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro102802 q ha hb
  have h8 (q : Pattern) (ha : d269464 q = 1) (hb : d332834 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d269464, d332834, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro102802 q ha hb
    | true =>
      simp only [d269464, d332834, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d269704 q = 1) (hb : d332991 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d269704, d332991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d269704, d332991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d269465 q = 1) (hb : d332835 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d269465, d332835, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d269465, d332835, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h11 (q : Pattern) (ha : d269705 q = 1) (hb : d332992 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d269705, d332992, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d269705, d332992, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d269706 q = 1) (hb : d332993 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d269706, d332993, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d269706, d332993, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d269707 q = 1) (hb : d332994 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d269707, d332994, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
    | true =>
      simp only [d269707, d332994, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d269712 q = 1) (hb : d332999 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d269712, d332999, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d269712, d332999, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h15 (q : Pattern) (ha : d269713 q = 1) (hb : d333000 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d269713, d333000, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d269713, d333000, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro102849 (p : Pattern) (ha : d269727 p = 1) (hb : d333000 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d38532 q = 1) (hb : d269718 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d38532, d269718, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d38532, d269718, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro102804 q ha hb
  have h2 (q : Pattern) (ha : d38178 q = 1) (hb : d269477 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d38178, d269477, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro102804 q ha hb
    | true =>
      simp only [d38178, d269477, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d38533 q = 1) (hb : d269719 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d38533, d269719, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d38533, d269719, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d38179 q = 1) (hb : d269478 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d38179, d269478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d38179, d269478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d38534 q = 1) (hb : d269720 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d38534, d269720, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d38534, d269720, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d38535 q = 1) (hb : d269721 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d38535, d269721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d38535, d269721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d269722 q = 1) (hb : d332990 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d269722, d332990, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d269722, d332990, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro102805 q ha hb
  have h8 (q : Pattern) (ha : d269482 q = 1) (hb : d332834 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d269482, d332834, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro102805 q ha hb
    | true =>
      simp only [d269482, d332834, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d269723 q = 1) (hb : d332991 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d269723, d332991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d269723, d332991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d269483 q = 1) (hb : d332835 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d269483, d332835, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d269483, d332835, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h11 (q : Pattern) (ha : d269724 q = 1) (hb : d332992 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d269724, d332992, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d269724, d332992, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d269725 q = 1) (hb : d332993 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d269725, d332993, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d269725, d332993, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d269726 q = 1) (hb : d332994 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d269726, d332994, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
    | true =>
      simp only [d269726, d332994, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d269703 q = 1) (hb : d332990 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d269703, d332990, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d269703, d332990, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro102802 q ha hb
  have h15 (q : Pattern) (ha : d269464 q = 1) (hb : d332834 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d269464, d332834, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro102802 q ha hb
    | true =>
      simp only [d269464, d332834, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h16 (q : Pattern) (ha : d269704 q = 1) (hb : d332991 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d269704, d332991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d269704, d332991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d269465 q = 1) (hb : d332835 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d269465, d332835, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d269465, d332835, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h18 (q : Pattern) (ha : d269705 q = 1) (hb : d332992 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d269705, d332992, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d269705, d332992, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d269706 q = 1) (hb : d332993 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d269706, d332993, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d269706, d332993, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h20 (q : Pattern) (ha : d269712 q = 1) (hb : d332999 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d269712, d332999, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d269712, d332999, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h21 (q : Pattern) (ha : d269727 q = 1) (hb : d333000 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d269727, d333000, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d269727, d333000, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
  exact h21 p ha hb
theorem andIntro102850 (p : Pattern) (ha : d269741 p = 1) (hb : d333010 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d269731 q = 1) (hb : d332990 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d269731, d332990, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d269731, d332990, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro102807 q ha hb
  have h2 (q : Pattern) (ha : d269496 q = 1) (hb : d332834 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d269496, d332834, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro102807 q ha hb
    | true =>
      simp only [d269496, d332834, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d269732 q = 1) (hb : d332991 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d269732, d332991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d269732, d332991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d269497 q = 1) (hb : d332835 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d269497, d332835, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d269497, d332835, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d269733 q = 1) (hb : d332992 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d269733, d332992, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d269733, d332992, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d269734 q = 1) (hb : d332993 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d269734, d332993, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d269734, d332993, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d269735 q = 1) (hb : d332999 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d269735, d332999, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d269735, d332999, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d269736 q = 1) (hb : d333005 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d269736, d333005, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d269736, d333005, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro102808 q ha hb
  have h9 (q : Pattern) (ha : d269505 q = 1) (hb : d332846 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d269505, d332846, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro102808 q ha hb
    | true =>
      simp only [d269505, d332846, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h10 (q : Pattern) (ha : d269737 q = 1) (hb : d333006 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d269737, d333006, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d269737, d333006, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d269506 q = 1) (hb : d332847 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d269506, d332847, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d269506, d332847, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d269738 q = 1) (hb : d333007 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d269738, d333007, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d269738, d333007, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d269739 q = 1) (hb : d333008 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d269739, d333008, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d269739, d333008, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h14 (q : Pattern) (ha : d269740 q = 1) (hb : d333009 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d269740, d333009, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d269740, d333009, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h15 (q : Pattern) (ha : d269741 q = 1) (hb : d333010 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d269741, d333010, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d269741, d333010, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro102851 (p : Pattern) (ha : d269747 p = 1) (hb : d333016 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d269709 q = 1) (hb : d332996 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d269709, d332996, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro82382 q hb ha
    | true =>
      simp only [d269709, d332996, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro102847 q ha hb
  have h2 (q : Pattern) (ha : d269710 q = 1) (hb : d332997 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d269710, d332997, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d269710, d332997, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d269711 q = 1) (hb : d332998 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d269711, d332998, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d269711, d332998, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d269714 q = 1) (hb : d333001 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d269714, d333001, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro102847 q ha hb
    | true =>
      simp only [d269714, d333001, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro102848 q ha hb
  have h5 (q : Pattern) (ha : d269715 q = 1) (hb : d333002 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d269715, d333002, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d269715, d333002, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d269716 q = 1) (hb : d333003 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d269716, d333003, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d269716, d333003, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d269717 q = 1) (hb : d333004 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d269717, d333004, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d269717, d333004, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d269728 q = 1) (hb : d333001 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d269728, d333001, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro102847 q ha hb
    | true =>
      simp only [d269728, d333001, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro102849 q ha hb
  have h9 (q : Pattern) (ha : d269729 q = 1) (hb : d333002 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d269729, d333002, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d269729, d333002, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d269730 q = 1) (hb : d333003 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d269730, d333003, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d269730, d333003, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d269742 q = 1) (hb : d333011 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d269742, d333011, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro102849 q ha hb
    | true =>
      simp only [d269742, d333011, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro102850 q ha hb
  have h12 (q : Pattern) (ha : d269743 q = 1) (hb : d333012 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d269743, d333012, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d269743, d333012, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d269744 q = 1) (hb : d333013 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d269744, d333013, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d269744, d333013, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d269745 q = 1) (hb : d333014 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d269745, d333014, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d269745, d333014, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d269746 q = 1) (hb : d333015 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d269746, d333015, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d269746, d333015, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d269747 q = 1) (hb : d333016 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d269747, d333016, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d269747, d333016, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h16 p ha hb
theorem andIntro102852 (p : Pattern) (ha : d269752 p = 1) (hb : d333021 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d269728 q = 1) (hb : d333001 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d269728, d333001, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro102847 q ha hb
    | true =>
      simp only [d269728, d333001, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro102849 q ha hb
  have h2 (q : Pattern) (ha : d269729 q = 1) (hb : d333002 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d269729, d333002, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d269729, d333002, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d269730 q = 1) (hb : d333003 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d269730, d333003, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d269730, d333003, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d269742 q = 1) (hb : d333011 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d269742, d333011, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro102849 q ha hb
    | true =>
      simp only [d269742, d333011, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro102850 q ha hb
  have h5 (q : Pattern) (ha : d269743 q = 1) (hb : d333012 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d269743, d333012, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d269743, d333012, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d269744 q = 1) (hb : d333013 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d269744, d333013, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d269744, d333013, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d269745 q = 1) (hb : d333014 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d269745, d333014, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d269745, d333014, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d269750 q = 1) (hb : d333019 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d269750, d333019, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d269750, d333019, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d269751 q = 1) (hb : d333020 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d269751, d333020, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d269751, d333020, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d269752 q = 1) (hb : d333021 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d269752, d333021, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d269752, d333021, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h10 p ha hb
theorem andIntro102853 (p : Pattern) (ha : d269758 p = 1) (hb : d333027 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d269748 q = 1) (hb : d333017 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d269748, d333017, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro102851 q ha hb
    | true =>
      simp only [d269748, d333017, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d269749 q = 1) (hb : d333018 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d269749, d333018, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d269749, d333018, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d269753 q = 1) (hb : d333022 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d269753, d333022, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro102852 q ha hb
    | true =>
      simp only [d269753, d333022, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d269754 q = 1) (hb : d333023 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d269754, d333023, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d269754, d333023, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d269755 q = 1) (hb : d333024 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d269755, d333024, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d269755, d333024, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d269756 q = 1) (hb : d333025 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d269756, d333025, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d269756, d333025, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d269757 q = 1) (hb : d333026 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d269757, d333026, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d269757, d333026, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d269758 q = 1) (hb : d333027 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d269758, d333027, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d269758, d333027, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro102854 (p : Pattern) (ha : d269760 p = 1) (hb : d333010 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d269722 q = 1) (hb : d332990 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d269722, d332990, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d269722, d332990, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro102805 q ha hb
  have h2 (q : Pattern) (ha : d269482 q = 1) (hb : d332834 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d269482, d332834, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro102805 q ha hb
    | true =>
      simp only [d269482, d332834, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d269723 q = 1) (hb : d332991 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d269723, d332991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d269723, d332991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d269483 q = 1) (hb : d332835 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d269483, d332835, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d269483, d332835, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d269724 q = 1) (hb : d332992 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d269724, d332992, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d269724, d332992, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d269725 q = 1) (hb : d332993 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d269725, d332993, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d269725, d332993, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d269759 q = 1) (hb : d332999 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d269759, d332999, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d269759, d332999, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d269736 q = 1) (hb : d333005 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d269736, d333005, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d269736, d333005, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro102808 q ha hb
  have h9 (q : Pattern) (ha : d269505 q = 1) (hb : d332846 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d269505, d332846, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro102808 q ha hb
    | true =>
      simp only [d269505, d332846, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h10 (q : Pattern) (ha : d269737 q = 1) (hb : d333006 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d269737, d333006, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d269737, d333006, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d269506 q = 1) (hb : d332847 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d269506, d332847, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d269506, d332847, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d269738 q = 1) (hb : d333007 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d269738, d333007, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d269738, d333007, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d269739 q = 1) (hb : d333008 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d269739, d333008, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d269739, d333008, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h14 (q : Pattern) (ha : d269740 q = 1) (hb : d333009 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d269740, d333009, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d269740, d333009, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h15 (q : Pattern) (ha : d269760 q = 1) (hb : d333010 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d269760, d333010, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d269760, d333010, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro102855 (p : Pattern) (ha : d269766 p = 1) (hb : d333029 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d269761 q = 1) (hb : d333011 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d269761, d333011, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro102849 q ha hb
    | true =>
      simp only [d269761, d333011, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro102854 q ha hb
  have h2 (q : Pattern) (ha : d269762 q = 1) (hb : d333012 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d269762, d333012, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d269762, d333012, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d269763 q = 1) (hb : d333013 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d269763, d333013, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d269763, d333013, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d269764 q = 1) (hb : d333019 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d269764, d333019, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d269764, d333019, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d269765 q = 1) (hb : d333028 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d269765, d333028, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d269765, d333028, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d269766 q = 1) (hb : d333029 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d269766, d333029, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d269766, d333029, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro102856 (p : Pattern) (ha : d269772 p = 1) (hb : d333035 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d269753 q = 1) (hb : d333022 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d269753, d333022, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro102852 q ha hb
    | true =>
      simp only [d269753, d333022, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d269754 q = 1) (hb : d333023 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d269754, d333023, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d269754, d333023, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d269767 q = 1) (hb : d333030 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d269767, d333030, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro102855 q ha hb
    | true =>
      simp only [d269767, d333030, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d269768 q = 1) (hb : d333031 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d269768, d333031, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d269768, d333031, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d269769 q = 1) (hb : d333032 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d269769, d333032, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d269769, d333032, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d269770 q = 1) (hb : d333033 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d269770, d333033, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d269770, d333033, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d269771 q = 1) (hb : d333034 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d269771, d333034, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d269771, d333034, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d269772 q = 1) (hb : d333035 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d269772, d333035, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d269772, d333035, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro102857 (p : Pattern) (ha : d269815 p = 1) (hb : d333038 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d38532 q = 1) (hb : d269718 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d38532, d269718, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d38532, d269718, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro102804 q ha hb
  have h2 (q : Pattern) (ha : d38178 q = 1) (hb : d269477 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d38178, d269477, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro102804 q ha hb
    | true =>
      simp only [d38178, d269477, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d38533 q = 1) (hb : d269719 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d38533, d269719, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d38533, d269719, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d38179 q = 1) (hb : d269478 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d38179, d269478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d38179, d269478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d38534 q = 1) (hb : d269720 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d38534, d269720, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d38534, d269720, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d38535 q = 1) (hb : d269721 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d38535, d269721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d38535, d269721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d269722 q = 1) (hb : d332990 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d269722, d332990, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d269722, d332990, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro102805 q ha hb
  have h8 (q : Pattern) (ha : d269482 q = 1) (hb : d332834 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d269482, d332834, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro102805 q ha hb
    | true =>
      simp only [d269482, d332834, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d269723 q = 1) (hb : d332991 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d269723, d332991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d269723, d332991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d269483 q = 1) (hb : d332835 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d269483, d332835, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d269483, d332835, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h11 (q : Pattern) (ha : d269724 q = 1) (hb : d332992 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d269724, d332992, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d269724, d332992, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d269725 q = 1) (hb : d332993 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d269725, d332993, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d269725, d332993, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d269726 q = 1) (hb : d332994 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d269726, d332994, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
    | true =>
      simp only [d269726, d332994, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d269810 q = 1) (hb : d325083 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d269810, d325083, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d269810, d325083, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro102828 q ha hb
  have h15 (q : Pattern) (ha : d269603 q = 1) (hb : d324967 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d269603, d324967, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro102828 q ha hb
    | true =>
      simp only [d269603, d324967, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h16 (q : Pattern) (ha : d269811 q = 1) (hb : d325084 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d269811, d325084, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d269811, d325084, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d269604 q = 1) (hb : d324968 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d269604, d324968, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d269604, d324968, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h18 (q : Pattern) (ha : d269812 q = 1) (hb : d325085 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d269812, d325085, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d269812, d325085, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d269813 q = 1) (hb : d325086 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d269813, d325086, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d269813, d325086, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h20 (q : Pattern) (ha : d269814 q = 1) (hb : d325087 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d269814, d325087, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d269814, d325087, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h21 (q : Pattern) (ha : d269815 q = 1) (hb : d333038 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d269815, d333038, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d269815, d333038, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
  exact h21 p ha hb
theorem andIntro102858 (p : Pattern) (ha : d269821 p = 1) (hb : d325089 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d269816 q = 1) (hb : d325083 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d269816, d325083, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d269816, d325083, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro102830 q ha hb
  have h2 (q : Pattern) (ha : d269610 q = 1) (hb : d324967 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d269610, d324967, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro102830 q ha hb
    | true =>
      simp only [d269610, d324967, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d269817 q = 1) (hb : d325084 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d269817, d325084, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d269817, d325084, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d269611 q = 1) (hb : d324968 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d269611, d324968, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d269611, d324968, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d269818 q = 1) (hb : d325085 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d269818, d325085, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d269818, d325085, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d269819 q = 1) (hb : d325086 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d269819, d325086, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d269819, d325086, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d269820 q = 1) (hb : d325087 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d269820, d325087, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d269820, d325087, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d269821 q = 1) (hb : d325089 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d269821, d325089, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d269821, d325089, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro102859 (p : Pattern) (ha : d269827 p = 1) (hb : d333044 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d269728 q = 1) (hb : d333001 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d269728, d333001, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro102847 q ha hb
    | true =>
      simp only [d269728, d333001, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro102849 q ha hb
  have h2 (q : Pattern) (ha : d269729 q = 1) (hb : d333002 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d269729, d333002, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d269729, d333002, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d269730 q = 1) (hb : d333003 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d269730, d333003, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d269730, d333003, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d269742 q = 1) (hb : d333011 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d269742, d333011, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro102849 q ha hb
    | true =>
      simp only [d269742, d333011, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro102850 q ha hb
  have h5 (q : Pattern) (ha : d269743 q = 1) (hb : d333012 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d269743, d333012, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d269743, d333012, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d269744 q = 1) (hb : d333013 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d269744, d333013, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d269744, d333013, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d269745 q = 1) (hb : d333014 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d269745, d333014, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d269745, d333014, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d269822 q = 1) (hb : d333039 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d269822, d333039, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro102857 q ha hb
    | true =>
      simp only [d269822, d333039, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro102858 q ha hb
  have h9 (q : Pattern) (ha : d269823 q = 1) (hb : d333040 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d269823, d333040, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d269823, d333040, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d269824 q = 1) (hb : d333041 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d269824, d333041, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d269824, d333041, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d269825 q = 1) (hb : d333042 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d269825, d333042, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d269825, d333042, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d269826 q = 1) (hb : d333043 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d269826, d333043, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d269826, d333043, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d269827 q = 1) (hb : d333044 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d269827, d333044, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d269827, d333044, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h13 p ha hb
theorem andIntro102860 (p : Pattern) (ha : d269833 p = 1) (hb : d333050 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d269828 q = 1) (hb : d333045 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d269828, d333045, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro102859 q ha hb
    | true =>
      simp only [d269828, d333045, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d269829 q = 1) (hb : d333046 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d269829, d333046, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d269829, d333046, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d269830 q = 1) (hb : d333047 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d269830, d333047, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d269830, d333047, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d269831 q = 1) (hb : d333048 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d269831, d333048, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d269831, d333048, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d269832 q = 1) (hb : d333049 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d269832, d333049, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d269832, d333049, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d269833 q = 1) (hb : d333050 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d269833, d333050, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d269833, d333050, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro102861 (p : Pattern) (ha : d269839 p = 1) (hb : d333056 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d269773 q = 1) (hb : d333036 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d269773, d333036, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro102853 q ha hb
    | true =>
      simp only [d269773, d333036, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro102856 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d269808 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d269809 q = 1) (hb : d333037 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d269809, d333037, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d269809, d333037, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d269834 q = 1) (hb : d333051 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d269834, d333051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro102860 q ha hb
    | true =>
      simp only [d269834, d333051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d269835 q = 1) (hb : d333052 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d269835, d333052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d269835, d333052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d269836 q = 1) (hb : d333053 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d269836, d333053, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d269836, d333053, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d269837 q = 1) (hb : d333054 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d269837, d333054, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d269837, d333054, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d269838 q = 1) (hb : d333055 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d269838, d333055, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d269838, d333055, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d269839 q = 1) (hb : d333056 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d269839, d333056, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d269839, d333056, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro102862 (p : Pattern) (ha : d269844 p = 1) (hb : d333061 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d269767 q = 1) (hb : d333030 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d269767, d333030, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro102855 q ha hb
    | true =>
      simp only [d269767, d333030, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d269768 q = 1) (hb : d333031 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d269768, d333031, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d269768, d333031, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d269841 q = 1) (hb : d333058 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d269841, d333058, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d269841, d333058, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d269842 q = 1) (hb : d333059 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d269842, d333059, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d269842, d333059, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d269843 q = 1) (hb : d333060 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d269843, d333060, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d269843, d333060, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d269844 q = 1) (hb : d333061 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d269844, d333061, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d269844, d333061, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro102863 (p : Pattern) (ha : d269850 p = 1) (hb : d333067 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d269845 q = 1) (hb : d333062 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d269845, d333062, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro102862 q ha hb
    | true =>
      simp only [d269845, d333062, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d269846 q = 1) (hb : d333063 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d269846, d333063, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d269846, d333063, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d269847 q = 1) (hb : d333064 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d269847, d333064, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d269847, d333064, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d269848 q = 1) (hb : d333065 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d269848, d333065, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d269848, d333065, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d269849 q = 1) (hb : d333066 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d269849, d333066, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d269849, d333066, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d269850 q = 1) (hb : d333067 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d269850, d333067, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d269850, d333067, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro102864 (p : Pattern) (ha : d269856 p = 1) (hb : d333073 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d269543 q = 1) (hb : d332879 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d269543, d332879, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d269543, d332879, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro102815 q ha hb
  have h2 (q : Pattern) (ha : d269544 q = 1) (hb : d332880 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d269544, d332880, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d269544, d332880, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d269553 q = 1) (hb : d332889 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d269553, d332889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro102815 q ha hb
    | true =>
      simp only [d269553, d332889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro102818 q ha hb
  have h4 (q : Pattern) (ha : d269554 q = 1) (hb : d332890 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d269554, d332890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d269554, d332890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d269555 q = 1) (hb : d332891 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d269555, d332891, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d269555, d332891, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d269656 q = 1) (hb : d332963 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d269656, d332963, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro102834 q ha hb
    | true =>
      simp only [d269656, d332963, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro102842 q ha hb
  have h7 (q : Pattern) (ha : d269674 q = 1) (hb : d332976 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d269674, d332976, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro102843 q ha hb
    | true =>
      simp only [d269674, d332976, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro102844 q ha hb
  have h8 (q : Pattern) (ha : d269675 q = 1) (hb : d332977 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d269675, d332977, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d269675, d332977, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d269676 q = 1) (hb : d332978 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d269676, d332978, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d269676, d332978, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h10 (q : Pattern) (ha : d269677 q = 1) (hb : d332979 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d269677, d332979, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d269677, d332979, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d269681 q = 1) (hb : d332983 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d269681, d332983, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d269681, d332983, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro102845 q ha hb
  have h12 (q : Pattern) (ha : d269683 q = 1) (hb : d332985 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d269683, d332985, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d269683, d332985, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro102846 q ha hb
  have h13 (q : Pattern) (ha : d269684 q = 1) (hb : d332986 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d269684, d332986, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d269684, d332986, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d269685 q = 1) (hb : d332987 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d269685, d332987, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d269685, d332987, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h15 (q : Pattern) (ha : d269686 q = 1) (hb : d332988 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d269686, d332988, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d269686, d332988, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h16 (q : Pattern) (ha : d269687 q = 1) (hb : d332989 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d269687, d332989, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d269687, d332989, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d269840 q = 1) (hb : d333057 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d269840, d333057, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d269840, d333057, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro102861 q ha hb
  have h18 (q : Pattern) (ha : d269851 q = 1) (hb : d333068 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d269851, d333068, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d269851, d333068, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro102863 q ha hb
  have h19 (q : Pattern) (ha : d269852 q = 1) (hb : d333069 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d269852, d333069, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d269852, d333069, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d269853 q = 1) (hb : d333070 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d269853, d333070, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d269853, d333070, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h21 (q : Pattern) (ha : d269854 q = 1) (hb : d333071 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d269854, d333071, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d269854, d333071, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h22 (q : Pattern) (ha : d269855 q = 1) (hb : d333072 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d269855, d333072, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d269855, d333072, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h23 (q : Pattern) (ha : d269856 q = 1) (hb : d333073 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d269856, d333073, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d269856, d333073, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
  exact h23 p ha hb
theorem andIntro102865 (p : Pattern) (ha : d269862 p = 1) (hb : d333079 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d269857 q = 1) (hb : d333074 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d269857, d333074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d269857, d333074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro102864 q ha hb
  have h2 (q : Pattern) (ha : d269858 q = 1) (hb : d333075 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d269858, d333075, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d269858, d333075, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d269859 q = 1) (hb : d333076 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d269859, d333076, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d269859, d333076, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d269860 q = 1) (hb : d333077 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d269860, d333077, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d269860, d333077, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d269861 q = 1) (hb : d333078 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d269861, d333078, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d269861, d333078, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d269862 q = 1) (hb : d333079 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d269862, d333079, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d269862, d333079, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro102866 (p : Pattern) (ha : d269868 p = 1) (hb : d333085 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d268313 q = 1) (hb : d331804 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d268313, d331804, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro102565 q ha hb
    | true =>
      simp only [d268313, d331804, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro102611 q ha hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d268585 q = 1) (hb : d332077 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d268585, d332077, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d268585, d332077, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro102664 q ha hb
  have h3 (q : Pattern) (ha : d268586 q = 1) (hb : d332078 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d268586, d332078, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d268586, d332078, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d268956 q = 1) (hb : d332453 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d268956, d332453, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d268956, d332453, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro102726 q ha hb
  have h5 (q : Pattern) (ha : d268957 q = 1) (hb : d332454 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d268957, d332454, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d268957, d332454, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d268958 q = 1) (hb : d332455 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d268958, d332455, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d268958, d332455, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d269422 q = 1) (hb : d332823 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d269422, d332823, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d269422, d332823, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro102800 q ha hb
  have h8 (q : Pattern) (ha : d269423 q = 1) (hb : d332824 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d269423, d332824, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d269423, d332824, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d269424 q = 1) (hb : d332825 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d269424, d332825, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d269424, d332825, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d269425 q = 1) (hb : d332826 q = 1) : d0 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d269425, d332826, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d269425, d332826, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d269863 q = 1) (hb : d333080 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d269863, d333080, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d269863, d333080, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro102865 q ha hb
  have h12 (q : Pattern) (ha : d269864 q = 1) (hb : d333081 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d269864, d333081, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d269864, d333081, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d269865 q = 1) (hb : d333082 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d269865, d333082, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d269865, d333082, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d269866 q = 1) (hb : d333083 q = 1) : d0 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d269866, d333083, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d269866, d333083, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d269867 q = 1) (hb : d333084 q = 1) : d0 q = 1 := by
    cases bit : q 10250 with
    | false =>
      simp only [d269867, d333084, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d269867, d333084, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d269868 q = 1) (hb : d333085 q = 1) : d0 q = 1 := by
    cases bit : q 260 with
    | false =>
      simp only [d269868, d333085, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d269868, d333085, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  exact h16 p ha hb
theorem andIntro102867 (p : Pattern) (ha : d269874 p = 1) (hb : d333091 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d269869 q = 1) (hb : d333086 q = 1) : d0 q = 1 := by
    cases bit : q 259 with
    | false =>
      simp only [d269869, d333086, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro102866 q ha hb
    | true =>
      simp only [d269869, d333086, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d269870 q = 1) (hb : d333087 q = 1) : d0 q = 1 := by
    cases bit : q 258 with
    | false =>
      simp only [d269870, d333087, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d269870, d333087, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d269871 q = 1) (hb : d333088 q = 1) : d0 q = 1 := by
    cases bit : q 257 with
    | false =>
      simp only [d269871, d333088, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d269871, d333088, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d269872 q = 1) (hb : d333089 q = 1) : d0 q = 1 := by
    cases bit : q 256 with
    | false =>
      simp only [d269872, d333089, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d269872, d333089, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d269873 q = 1) (hb : d333090 q = 1) : d0 q = 1 := by
    cases bit : q 255 with
    | false =>
      simp only [d269873, d333090, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d269873, d333090, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d269874 q = 1) (hb : d333091 q = 1) : d0 q = 1 := by
    cases bit : q 254 with
    | false =>
      simp only [d269874, d333091, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d269874, d333091, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro102868 (p : Pattern) (ha : d269880 p = 1) (hb : d333097 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d269875 q = 1) (hb : d333092 q = 1) : d0 q = 1 := by
    cases bit : q 253 with
    | false =>
      simp only [d269875, d333092, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro102867 q ha hb
    | true =>
      simp only [d269875, d333092, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d269876 q = 1) (hb : d333093 q = 1) : d0 q = 1 := by
    cases bit : q 252 with
    | false =>
      simp only [d269876, d333093, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d269876, d333093, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d269877 q = 1) (hb : d333094 q = 1) : d0 q = 1 := by
    cases bit : q 251 with
    | false =>
      simp only [d269877, d333094, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d269877, d333094, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d269878 q = 1) (hb : d333095 q = 1) : d0 q = 1 := by
    cases bit : q 250 with
    | false =>
      simp only [d269878, d333095, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d269878, d333095, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d269879 q = 1) (hb : d333096 q = 1) : d0 q = 1 := by
    cases bit : q 249 with
    | false =>
      simp only [d269879, d333096, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d269879, d333096, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d269880 q = 1) (hb : d333097 q = 1) : d0 q = 1 := by
    cases bit : q 245 with
    | false =>
      simp only [d269880, d333097, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d269880, d333097, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro102869 (p : Pattern) (ha : d269886 p = 1) (hb : d333103 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d269881 q = 1) (hb : d333098 q = 1) : d0 q = 1 := by
    cases bit : q 200 with
    | false =>
      simp only [d269881, d333098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro102868 q ha hb
    | true =>
      simp only [d269881, d333098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d269882 q = 1) (hb : d333099 q = 1) : d0 q = 1 := by
    cases bit : q 199 with
    | false =>
      simp only [d269882, d333099, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d269882, d333099, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d269883 q = 1) (hb : d333100 q = 1) : d0 q = 1 := by
    cases bit : q 186 with
    | false =>
      simp only [d269883, d333100, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d269883, d333100, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d269884 q = 1) (hb : d333101 q = 1) : d0 q = 1 := by
    cases bit : q 185 with
    | false =>
      simp only [d269884, d333101, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d269884, d333101, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d269885 q = 1) (hb : d333102 q = 1) : d0 q = 1 := by
    cases bit : q 184 with
    | false =>
      simp only [d269885, d333102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d269885, d333102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d269886 q = 1) (hb : d333103 q = 1) : d0 q = 1 := by
    cases bit : q 181 with
    | false =>
      simp only [d269886, d333103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d269886, d333103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro102870 (p : Pattern) (ha : d269892 p = 1) (hb : d333109 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d269887 q = 1) (hb : d333104 q = 1) : d0 q = 1 := by
    cases bit : q 177 with
    | false =>
      simp only [d269887, d333104, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro102869 q ha hb
    | true =>
      simp only [d269887, d333104, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d269888 q = 1) (hb : d333105 q = 1) : d0 q = 1 := by
    cases bit : q 164 with
    | false =>
      simp only [d269888, d333105, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d269888, d333105, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d269889 q = 1) (hb : d333106 q = 1) : d0 q = 1 := by
    cases bit : q 156 with
    | false =>
      simp only [d269889, d333106, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d269889, d333106, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d269890 q = 1) (hb : d333107 q = 1) : d0 q = 1 := by
    cases bit : q 155 with
    | false =>
      simp only [d269890, d333107, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d269890, d333107, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d269891 q = 1) (hb : d333108 q = 1) : d0 q = 1 := by
    cases bit : q 134 with
    | false =>
      simp only [d269891, d333108, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d269891, d333108, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d269892 q = 1) (hb : d333109 q = 1) : d0 q = 1 := by
    cases bit : q 133 with
    | false =>
      simp only [d269892, d333109, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d269892, d333109, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro102871 (p : Pattern) (ha : d269898 p = 1) (hb : d333115 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d269893 q = 1) (hb : d333110 q = 1) : d0 q = 1 := by
    cases bit : q 120 with
    | false =>
      simp only [d269893, d333110, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro102870 q ha hb
    | true =>
      simp only [d269893, d333110, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d269894 q = 1) (hb : d333111 q = 1) : d0 q = 1 := by
    cases bit : q 118 with
    | false =>
      simp only [d269894, d333111, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d269894, d333111, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d269895 q = 1) (hb : d333112 q = 1) : d0 q = 1 := by
    cases bit : q 114 with
    | false =>
      simp only [d269895, d333112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d269895, d333112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d269896 q = 1) (hb : d333113 q = 1) : d0 q = 1 := by
    cases bit : q 111 with
    | false =>
      simp only [d269896, d333113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d269896, d333113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d269897 q = 1) (hb : d333114 q = 1) : d0 q = 1 := by
    cases bit : q 98 with
    | false =>
      simp only [d269897, d333114, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d269897, d333114, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d269898 q = 1) (hb : d333115 q = 1) : d0 q = 1 := by
    cases bit : q 97 with
    | false =>
      simp only [d269898, d333115, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d269898, d333115, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro102872 (p : Pattern) (ha : d269904 p = 1) (hb : d333121 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d269899 q = 1) (hb : d333116 q = 1) : d0 q = 1 := by
    cases bit : q 94 with
    | false =>
      simp only [d269899, d333116, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro102871 q ha hb
    | true =>
      simp only [d269899, d333116, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d269900 q = 1) (hb : d333117 q = 1) : d0 q = 1 := by
    cases bit : q 76 with
    | false =>
      simp only [d269900, d333117, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d269900, d333117, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d269901 q = 1) (hb : d333118 q = 1) : d0 q = 1 := by
    cases bit : q 67 with
    | false =>
      simp only [d269901, d333118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d269901, d333118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d269902 q = 1) (hb : d333119 q = 1) : d0 q = 1 := by
    cases bit : q 52 with
    | false =>
      simp only [d269902, d333119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d269902, d333119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d269903 q = 1) (hb : d333120 q = 1) : d0 q = 1 := by
    cases bit : q 47 with
    | false =>
      simp only [d269903, d333120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d269903, d333120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d269904 q = 1) (hb : d333121 q = 1) : d0 q = 1 := by
    cases bit : q 46 with
    | false =>
      simp only [d269904, d333121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d269904, d333121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro102873 (p : Pattern) (ha : d269910 p = 1) (hb : d333127 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d269905 q = 1) (hb : d333122 q = 1) : d0 q = 1 := by
    cases bit : q 45 with
    | false =>
      simp only [d269905, d333122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro102872 q ha hb
    | true =>
      simp only [d269905, d333122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d269906 q = 1) (hb : d333123 q = 1) : d0 q = 1 := by
    cases bit : q 30 with
    | false =>
      simp only [d269906, d333123, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d269906, d333123, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d269907 q = 1) (hb : d333124 q = 1) : d0 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d269907, d333124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d269907, d333124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d269908 q = 1) (hb : d333125 q = 1) : d0 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d269908, d333125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d269908, d333125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d269909 q = 1) (hb : d333126 q = 1) : d0 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d269909, d333126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d269909, d333126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d269910 q = 1) (hb : d333127 q = 1) : d0 q = 1 := by
    cases bit : q 25 with
    | false =>
      simp only [d269910, d333127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d269910, d333127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro102874 (p : Pattern) (ha : d309695 p = 1) (hb : d331335 p = 1) : d333269 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d331335 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d44509 q = 1) (hb : d331335 q = 1) : d332883 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d44509, d332883, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro102193 q ha hb
    | true =>
      simp only [d44509, d332883, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro102194 q ha hb
  have h2 (q : Pattern) (ha : d44510 q = 1) (hb : d331335 q = 1) : d332884 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d44510, d332884, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d44510, d332884, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d44511 q = 1) (hb : d331335 q = 1) : d332885 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d44511, d332885, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d44511, d332885, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d44512 q = 1) (hb : d331335 q = 1) : d332886 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d44512, d332886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d44512, d332886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d44513 q = 1) (hb : d331335 q = 1) : d332887 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d44513, d332887, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d44513, d332887, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d309695 q = 1) (hb : d331335 q = 1) : d333269 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d309695, d333269, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d309695, d333269, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro102875 (p : Pattern) (ha : d309706 p = 1) (hb : d331335 p = 1) : d333280 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d331335 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d309701 q = 1) (hb : d331335 q = 1) : d333275 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d309701, d333275, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro102230 q ha hb
    | true =>
      simp only [d309701, d333275, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro102202 q ha hb
  have h2 (q : Pattern) (ha : d309702 q = 1) (hb : d331335 q = 1) : d333276 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d309702, d333276, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d309702, d333276, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d309703 q = 1) (hb : d331335 q = 1) : d333277 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d309703, d333277, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d309703, d333277, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d309704 q = 1) (hb : d331335 q = 1) : d333278 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d309704, d333278, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d309704, d333278, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d309705 q = 1) (hb : d331335 q = 1) : d333279 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d309705, d333279, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d309705, d333279, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d309706 q = 1) (hb : d331335 q = 1) : d333280 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d309706, d333280, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d309706, d333280, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro102876 (p : Pattern) (ha : d309712 p = 1) (hb : d331335 p = 1) : d333286 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d331335 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d44515 q = 1) (hb : d331335 q = 1) : d332889 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d44515, d332889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro102192 q ha hb
    | true =>
      simp only [d44515, d332889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro102195 q ha hb
  have h2 (q : Pattern) (ha : d44516 q = 1) (hb : d331335 q = 1) : d332890 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d44516, d332890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d44516, d332890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d309693 q = 1) (hb : d331335 q = 1) : d333267 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d309693, d333267, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d309693, d333267, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d309694 q = 1) (hb : d331335 q = 1) : d333268 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d309694, d333268, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d309694, d333268, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d309696 q = 1) (hb : d331335 q = 1) : d333270 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d309696, d333270, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d309696, d333270, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro102874 q ha hb
  have h6 (q : Pattern) (ha : d309697 q = 1) (hb : d331335 q = 1) : d333271 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d309697, d333271, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d309697, d333271, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d309698 q = 1) (hb : d331335 q = 1) : d333272 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d309698, d333272, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d309698, d333272, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d309699 q = 1) (hb : d331335 q = 1) : d333273 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d309699, d333273, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d309699, d333273, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d309700 q = 1) (hb : d331335 q = 1) : d333274 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d309700, d333274, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d309700, d333274, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d309707 q = 1) (hb : d331335 q = 1) : d333281 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d309707, d333281, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d309707, d333281, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro102875 q ha hb
  have h11 (q : Pattern) (ha : d309708 q = 1) (hb : d331335 q = 1) : d333282 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d309708, d333282, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d309708, d333282, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d309709 q = 1) (hb : d331335 q = 1) : d333283 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d309709, d333283, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d309709, d333283, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d309710 q = 1) (hb : d331335 q = 1) : d333284 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d309710, d333284, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d309710, d333284, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d309711 q = 1) (hb : d331335 q = 1) : d333285 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d309711, d333285, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d309711, d333285, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d309712 q = 1) (hb : d331335 q = 1) : d333286 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d309712, d333286, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d309712, d333286, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro102877 (p : Pattern) (ha : d309718 p = 1) (hb : d331335 p = 1) : d333292 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d331335 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d309713 q = 1) (hb : d331335 q = 1) : d333287 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d309713, d333287, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d309713, d333287, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro102876 q ha hb
  have h2 (q : Pattern) (ha : d309714 q = 1) (hb : d331335 q = 1) : d333288 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d309714, d333288, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d309714, d333288, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d309715 q = 1) (hb : d331335 q = 1) : d333289 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d309715, d333289, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d309715, d333289, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d309716 q = 1) (hb : d331335 q = 1) : d333290 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d309716, d333290, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d309716, d333290, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d309717 q = 1) (hb : d331335 q = 1) : d333291 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d309717, d333291, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d309717, d333291, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d309718 q = 1) (hb : d331335 q = 1) : d333292 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d309718, d333292, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d309718, d333292, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro102878 (p : Pattern) (ha : d331335 p = 1) (hb : d357418 p = 1) : d333130 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d331335 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d49 q = 1) (hb : d331335 q = 1) : d49 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d42281 q = 1) (hb : d331335 q = 1) : d331368 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d42281, d331368, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro102244 q ha hb
    | true =>
      simp only [d42281, d331368, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d42341 q = 1) (hb : d331335 q = 1) : d331428 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d42341, d331428, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d42341, d331428, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d42342 q = 1) (hb : d331335 q = 1) : d331429 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d42342, d331429, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d42342, d331429, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d42343 q = 1) (hb : d331335 q = 1) : d331430 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d42343, d331430, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d42343, d331430, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d42344 q = 1) (hb : d331335 q = 1) : d331431 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d42344, d331431, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d42344, d331431, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d331335 q = 1) (hb : d357418 q = 1) : d333130 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d357418, d333130, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d357418, d333130, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  exact h7 p ha hb
theorem andIntro102879 (p : Pattern) (ha : d331335 p = 1) (hb : d357428 p = 1) : d333140 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d331335 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d83 q = 1) (hb : d331335 q = 1) : d83 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d42317 q = 1) (hb : d331335 q = 1) : d331404 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d42317, d331404, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro102249 q ha hb
    | true =>
      simp only [d42317, d331404, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d331335 q = 1) (hb : d357424 q = 1) : d333136 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d357424, d333136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d357424, d333136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d331335 q = 1) (hb : d357425 q = 1) : d333137 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d357425, d333137, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d357425, d333137, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d331335 q = 1) (hb : d357426 q = 1) : d333138 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d357426, d333138, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d357426, d333138, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d331335 q = 1) (hb : d357427 q = 1) : d333139 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d357427, d333139, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d357427, d333139, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d331335 q = 1) (hb : d357428 q = 1) : d333140 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d357428, d333140, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d357428, d333140, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro102880 (p : Pattern) (ha : d331335 p = 1) (hb : d357434 p = 1) : d333146 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d331335 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d42346 q = 1) (hb : d331335 q = 1) : d331433 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d42346, d331433, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro102252 q ha hb
    | true =>
      simp only [d42346, d331433, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro102253 q ha hb
  have h2 (q : Pattern) (ha : d42347 q = 1) (hb : d331335 q = 1) : d331434 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d42347, d331434, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d42347, d331434, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d331335 q = 1) (hb : d357416 q = 1) : d333128 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d357416, d333128, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d357416, d333128, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d331335 q = 1) (hb : d357417 q = 1) : d333129 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d357417, d333129, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d357417, d333129, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d331335 q = 1) (hb : d357419 q = 1) : d333131 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d357419, d333131, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d357419, d333131, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro102878 q ha hb
  have h6 (q : Pattern) (ha : d331335 q = 1) (hb : d357420 q = 1) : d333132 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d357420, d333132, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d357420, d333132, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d331335 q = 1) (hb : d357421 q = 1) : d333133 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d357421, d333133, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d357421, d333133, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d331335 q = 1) (hb : d357422 q = 1) : d333134 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d357422, d333134, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d357422, d333134, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d331335 q = 1) (hb : d357423 q = 1) : d333135 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d357423, d333135, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d357423, d333135, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d331335 q = 1) (hb : d357429 q = 1) : d333141 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d357429, d333141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d357429, d333141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro102879 q ha hb
  have h11 (q : Pattern) (ha : d331335 q = 1) (hb : d357430 q = 1) : d333142 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d357430, d333142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d357430, d333142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d331335 q = 1) (hb : d357431 q = 1) : d333143 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d357431, d333143, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d357431, d333143, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d331335 q = 1) (hb : d357432 q = 1) : d333144 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d357432, d333144, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d357432, d333144, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h14 (q : Pattern) (ha : d331335 q = 1) (hb : d357433 q = 1) : d333145 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d357433, d333145, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d357433, d333145, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h15 (q : Pattern) (ha : d331335 q = 1) (hb : d357434 q = 1) : d333146 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d357434, d333146, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d357434, d333146, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro102881 (p : Pattern) (ha : d331335 p = 1) (hb : d357440 p = 1) : d333152 p = 1 := by
  have h0 (q : Pattern) (ha : d53652 q = 1) (hb : d331335 q = 1) : d53652 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d331335 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d331335 q = 1) (hb : d357435 q = 1) : d333147 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d357435, d333147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d357435, d333147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro102880 q ha hb
  have h3 (q : Pattern) (ha : d331335 q = 1) (hb : d357436 q = 1) : d333148 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d357436, d333148, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d357436, d333148, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d331335 q = 1) (hb : d357437 q = 1) : d333149 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d357437, d333149, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d357437, d333149, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d331335 q = 1) (hb : d357438 q = 1) : d333150 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d357438, d333150, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d357438, d333150, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d331335 q = 1) (hb : d357439 q = 1) : d333151 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d357439, d333151, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d357439, d333151, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d331335 q = 1) (hb : d357440 q = 1) : d333152 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d357440, d333152, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d357440, d333152, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro102882 (p : Pattern) (ha : d331335 p = 1) (hb : d357443 p = 1) : d333155 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d331335 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d42565 q = 1) (hb : d331335 q = 1) : d331600 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d42565, d331600, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro102283 q ha hb
    | true =>
      simp only [d42565, d331600, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro102284 q ha hb
  have h2 (q : Pattern) (ha : d42566 q = 1) (hb : d331335 q = 1) : d331601 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d42566, d331601, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d42566, d331601, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d42567 q = 1) (hb : d331335 q = 1) : d331602 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d42567, d331602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d42567, d331602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d42568 q = 1) (hb : d331335 q = 1) : d331603 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d42568, d331603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d42568, d331603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d42569 q = 1) (hb : d331335 q = 1) : d331604 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d42569, d331604, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d42569, d331604, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d331335 q = 1) (hb : d357443 q = 1) : d333155 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d357443, d333155, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d357443, d333155, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  exact h6 p ha hb
theorem andIntro102883 (p : Pattern) (ha : d331335 p = 1) (hb : d357454 p = 1) : d333166 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d331335 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d331335 q = 1) (hb : d357449 q = 1) : d333161 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d357449, d333161, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro102320 q hb ha
    | true =>
      simp only [d357449, d333161, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro102290 q hb ha
  have h2 (q : Pattern) (ha : d331335 q = 1) (hb : d357450 q = 1) : d333162 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d357450, d333162, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d357450, d333162, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d331335 q = 1) (hb : d357451 q = 1) : d333163 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d357451, d333163, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d357451, d333163, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d331335 q = 1) (hb : d357452 q = 1) : d333164 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d357452, d333164, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d357452, d333164, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d331335 q = 1) (hb : d357453 q = 1) : d333165 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d357453, d333165, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d357453, d333165, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d331335 q = 1) (hb : d357454 q = 1) : d333166 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d357454, d333166, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d357454, d333166, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro102884 (p : Pattern) (ha : d331335 p = 1) (hb : d357460 p = 1) : d333172 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d331335 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d42571 q = 1) (hb : d331335 q = 1) : d331606 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d42571, d331606, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro102282 q ha hb
    | true =>
      simp only [d42571, d331606, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro102285 q ha hb
  have h2 (q : Pattern) (ha : d42572 q = 1) (hb : d331335 q = 1) : d331607 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d42572, d331607, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d42572, d331607, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d331335 q = 1) (hb : d357441 q = 1) : d333153 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d357441, d333153, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d357441, d333153, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d331335 q = 1) (hb : d357442 q = 1) : d333154 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d357442, d333154, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d357442, d333154, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d331335 q = 1) (hb : d357444 q = 1) : d333156 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d357444, d333156, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d357444, d333156, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro102882 q ha hb
  have h6 (q : Pattern) (ha : d331335 q = 1) (hb : d357445 q = 1) : d333157 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d357445, d333157, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d357445, d333157, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d331335 q = 1) (hb : d357446 q = 1) : d333158 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d357446, d333158, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d357446, d333158, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d331335 q = 1) (hb : d357447 q = 1) : d333159 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d357447, d333159, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d357447, d333159, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d331335 q = 1) (hb : d357448 q = 1) : d333160 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d357448, d333160, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d357448, d333160, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d331335 q = 1) (hb : d357455 q = 1) : d333167 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d357455, d333167, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d357455, d333167, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro102883 q ha hb
  have h11 (q : Pattern) (ha : d331335 q = 1) (hb : d357456 q = 1) : d333168 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d357456, d333168, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d357456, d333168, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d331335 q = 1) (hb : d357457 q = 1) : d333169 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d357457, d333169, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d357457, d333169, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d331335 q = 1) (hb : d357458 q = 1) : d333170 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d357458, d333170, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d357458, d333170, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h14 (q : Pattern) (ha : d331335 q = 1) (hb : d357459 q = 1) : d333171 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d357459, d333171, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d357459, d333171, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h15 (q : Pattern) (ha : d331335 q = 1) (hb : d357460 q = 1) : d333172 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d357460, d333172, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d357460, d333172, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro102885 (p : Pattern) (ha : d331335 p = 1) (hb : d357466 p = 1) : d333178 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d331335 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d331335 q = 1) (hb : d357461 q = 1) : d333173 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d357461, d333173, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d357461, d333173, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro102884 q ha hb
  have h2 (q : Pattern) (ha : d331335 q = 1) (hb : d357462 q = 1) : d333174 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d357462, d333174, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d357462, d333174, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d331335 q = 1) (hb : d357463 q = 1) : d333175 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d357463, d333175, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d357463, d333175, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d331335 q = 1) (hb : d357464 q = 1) : d333176 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d357464, d333176, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d357464, d333176, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d331335 q = 1) (hb : d357465 q = 1) : d333177 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d357465, d333177, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d357465, d333177, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d331335 q = 1) (hb : d357466 q = 1) : d333178 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d357466, d333178, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d357466, d333178, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro102886 (p : Pattern) (ha : d331335 p = 1) (hb : d357470 p = 1) : d333182 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d331335 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d42909 q = 1) (hb : d331335 q = 1) : d331850 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d42909, d331850, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro102334 q ha hb
    | true =>
      simp only [d42909, d331850, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro102335 q ha hb
  have h2 (q : Pattern) (ha : d42910 q = 1) (hb : d331335 q = 1) : d331851 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d42910, d331851, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d42910, d331851, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d42911 q = 1) (hb : d331335 q = 1) : d331852 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d42911, d331852, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d42911, d331852, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d42912 q = 1) (hb : d331335 q = 1) : d331853 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d42912, d331853, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d42912, d331853, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d42913 q = 1) (hb : d331335 q = 1) : d331854 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d42913, d331854, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d42913, d331854, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d331335 q = 1) (hb : d357470 q = 1) : d333182 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d357470, d333182, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d357470, d333182, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  exact h6 p ha hb
theorem andIntro102887 (p : Pattern) (ha : d331335 p = 1) (hb : d357481 p = 1) : d333193 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d331335 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d331335 q = 1) (hb : d357476 q = 1) : d333188 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d357476, d333188, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro102376 q hb ha
    | true =>
      simp only [d357476, d333188, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro102343 q hb ha
  have h2 (q : Pattern) (ha : d331335 q = 1) (hb : d357477 q = 1) : d333189 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d357477, d333189, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d357477, d333189, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d331335 q = 1) (hb : d357478 q = 1) : d333190 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d357478, d333190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d357478, d333190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d331335 q = 1) (hb : d357479 q = 1) : d333191 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d357479, d333191, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d357479, d333191, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d331335 q = 1) (hb : d357480 q = 1) : d333192 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d357480, d333192, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d357480, d333192, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d331335 q = 1) (hb : d357481 q = 1) : d333193 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d357481, d333193, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d357481, d333193, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro102888 (p : Pattern) (ha : d331335 p = 1) (hb : d357487 p = 1) : d333199 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d331335 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d42915 q = 1) (hb : d331335 q = 1) : d331856 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d42915, d331856, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro102333 q ha hb
    | true =>
      simp only [d42915, d331856, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro102336 q ha hb
  have h2 (q : Pattern) (ha : d42916 q = 1) (hb : d331335 q = 1) : d331857 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d42916, d331857, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d42916, d331857, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d331335 q = 1) (hb : d357468 q = 1) : d333180 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d357468, d333180, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d357468, d333180, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d331335 q = 1) (hb : d357469 q = 1) : d333181 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d357469, d333181, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d357469, d333181, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d331335 q = 1) (hb : d357471 q = 1) : d333183 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d357471, d333183, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d357471, d333183, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro102886 q ha hb
  have h6 (q : Pattern) (ha : d331335 q = 1) (hb : d357472 q = 1) : d333184 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d357472, d333184, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d357472, d333184, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d331335 q = 1) (hb : d357473 q = 1) : d333185 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d357473, d333185, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d357473, d333185, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d331335 q = 1) (hb : d357474 q = 1) : d333186 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d357474, d333186, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d357474, d333186, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d331335 q = 1) (hb : d357475 q = 1) : d333187 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d357475, d333187, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d357475, d333187, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d331335 q = 1) (hb : d357482 q = 1) : d333194 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d357482, d333194, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d357482, d333194, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro102887 q ha hb
  have h11 (q : Pattern) (ha : d331335 q = 1) (hb : d357483 q = 1) : d333195 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d357483, d333195, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d357483, d333195, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d331335 q = 1) (hb : d357484 q = 1) : d333196 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d357484, d333196, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d357484, d333196, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d331335 q = 1) (hb : d357485 q = 1) : d333197 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d357485, d333197, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d357485, d333197, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h14 (q : Pattern) (ha : d331335 q = 1) (hb : d357486 q = 1) : d333198 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d357486, d333198, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d357486, d333198, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h15 (q : Pattern) (ha : d331335 q = 1) (hb : d357487 q = 1) : d333199 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d357487, d333199, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d357487, d333199, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro102889 (p : Pattern) (ha : d331335 p = 1) (hb : d357493 p = 1) : d333205 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d331335 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d331335 q = 1) (hb : d357488 q = 1) : d333200 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d357488, d333200, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d357488, d333200, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro102888 q ha hb
  have h2 (q : Pattern) (ha : d331335 q = 1) (hb : d357489 q = 1) : d333201 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d357489, d333201, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d357489, d333201, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d331335 q = 1) (hb : d357490 q = 1) : d333202 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d357490, d333202, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d357490, d333202, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d331335 q = 1) (hb : d357491 q = 1) : d333203 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d357491, d333203, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d357491, d333203, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d331335 q = 1) (hb : d357492 q = 1) : d333204 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d357492, d333204, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d357492, d333204, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d331335 q = 1) (hb : d357493 q = 1) : d333205 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d357493, d333205, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d357493, d333205, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro102890 (p : Pattern) (ha : d331335 p = 1) (hb : d357498 p = 1) : d333210 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d331335 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d43379 q = 1) (hb : d331335 q = 1) : d332178 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d43379, d332178, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro102395 q ha hb
    | true =>
      simp only [d43379, d332178, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro102396 q ha hb
  have h2 (q : Pattern) (ha : d43380 q = 1) (hb : d331335 q = 1) : d332179 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d43380, d332179, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d43380, d332179, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d43381 q = 1) (hb : d331335 q = 1) : d332180 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d43381, d332180, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d43381, d332180, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d43382 q = 1) (hb : d331335 q = 1) : d332181 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d43382, d332181, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d43382, d332181, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d43383 q = 1) (hb : d331335 q = 1) : d332182 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d43383, d332182, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d43383, d332182, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d331335 q = 1) (hb : d357498 q = 1) : d333210 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d357498, d333210, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d357498, d333210, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  exact h6 p ha hb
theorem andIntro102891 (p : Pattern) (ha : d331335 p = 1) (hb : d357509 p = 1) : d333221 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d331335 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d331335 q = 1) (hb : d357504 q = 1) : d333216 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d357504, d333216, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro102437 q hb ha
    | true =>
      simp only [d357504, d333216, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro102404 q hb ha
  have h2 (q : Pattern) (ha : d331335 q = 1) (hb : d357505 q = 1) : d333217 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d357505, d333217, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d357505, d333217, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d331335 q = 1) (hb : d357506 q = 1) : d333218 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d357506, d333218, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d357506, d333218, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d331335 q = 1) (hb : d357507 q = 1) : d333219 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d357507, d333219, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d357507, d333219, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d331335 q = 1) (hb : d357508 q = 1) : d333220 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d357508, d333220, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d357508, d333220, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d331335 q = 1) (hb : d357509 q = 1) : d333221 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d357509, d333221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d357509, d333221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro102892 (p : Pattern) (ha : d331335 p = 1) (hb : d357515 p = 1) : d333227 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d331335 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d43385 q = 1) (hb : d331335 q = 1) : d332184 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d43385, d332184, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro102394 q ha hb
    | true =>
      simp only [d43385, d332184, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro102397 q ha hb
  have h2 (q : Pattern) (ha : d43386 q = 1) (hb : d331335 q = 1) : d332185 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d43386, d332185, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d43386, d332185, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d331335 q = 1) (hb : d357496 q = 1) : d333208 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d357496, d333208, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d357496, d333208, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d331335 q = 1) (hb : d357497 q = 1) : d333209 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d357497, d333209, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d357497, d333209, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d331335 q = 1) (hb : d357499 q = 1) : d333211 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d357499, d333211, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d357499, d333211, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro102890 q ha hb
  have h6 (q : Pattern) (ha : d331335 q = 1) (hb : d357500 q = 1) : d333212 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d357500, d333212, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d357500, d333212, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d331335 q = 1) (hb : d357501 q = 1) : d333213 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d357501, d333213, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d357501, d333213, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d331335 q = 1) (hb : d357502 q = 1) : d333214 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d357502, d333214, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d357502, d333214, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d331335 q = 1) (hb : d357503 q = 1) : d333215 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d357503, d333215, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d357503, d333215, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d331335 q = 1) (hb : d357510 q = 1) : d333222 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d357510, d333222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d357510, d333222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro102891 q ha hb
  have h11 (q : Pattern) (ha : d331335 q = 1) (hb : d357511 q = 1) : d333223 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d357511, d333223, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d357511, d333223, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d331335 q = 1) (hb : d357512 q = 1) : d333224 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d357512, d333224, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d357512, d333224, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d331335 q = 1) (hb : d357513 q = 1) : d333225 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d357513, d333225, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d357513, d333225, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h14 (q : Pattern) (ha : d331335 q = 1) (hb : d357514 q = 1) : d333226 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d357514, d333226, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d357514, d333226, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h15 (q : Pattern) (ha : d331335 q = 1) (hb : d357515 q = 1) : d333227 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d357515, d333227, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d357515, d333227, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro102893 (p : Pattern) (ha : d331335 p = 1) (hb : d357521 p = 1) : d333233 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d331335 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d331335 q = 1) (hb : d357516 q = 1) : d333228 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d357516, d333228, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d357516, d333228, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro102892 q ha hb
  have h2 (q : Pattern) (ha : d331335 q = 1) (hb : d357517 q = 1) : d333229 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d357517, d333229, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d357517, d333229, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d331335 q = 1) (hb : d357518 q = 1) : d333230 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d357518, d333230, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d357518, d333230, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d331335 q = 1) (hb : d357519 q = 1) : d333231 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d357519, d333231, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d357519, d333231, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d331335 q = 1) (hb : d357520 q = 1) : d333232 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d357520, d333232, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d357520, d333232, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d331335 q = 1) (hb : d357521 q = 1) : d333233 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d357521, d333233, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d357521, d333233, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro102894 (p : Pattern) (ha : d331335 p = 1) (hb : d357527 p = 1) : d333239 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d331335 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d43964 q = 1) (hb : d331335 q = 1) : d332550 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d43964, d332550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro102466 q ha hb
    | true =>
      simp only [d43964, d332550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro102467 q ha hb
  have h2 (q : Pattern) (ha : d43965 q = 1) (hb : d331335 q = 1) : d332551 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d43965, d332551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d43965, d332551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d43966 q = 1) (hb : d331335 q = 1) : d332552 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d43966, d332552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d43966, d332552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d43967 q = 1) (hb : d331335 q = 1) : d332553 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d43967, d332553, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d43967, d332553, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d43968 q = 1) (hb : d331335 q = 1) : d332554 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d43968, d332554, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d43968, d332554, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d331335 q = 1) (hb : d357527 q = 1) : d333239 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d357527, d333239, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d357527, d333239, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  exact h6 p ha hb
theorem andIntro102895 (p : Pattern) (ha : d331335 p = 1) (hb : d357538 p = 1) : d333250 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d331335 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d331335 q = 1) (hb : d357533 q = 1) : d333245 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d357533, d333245, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro102510 q hb ha
    | true =>
      simp only [d357533, d333245, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro102475 q hb ha
  have h2 (q : Pattern) (ha : d331335 q = 1) (hb : d357534 q = 1) : d333246 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d357534, d333246, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d357534, d333246, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d331335 q = 1) (hb : d357535 q = 1) : d333247 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d357535, d333247, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d357535, d333247, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d331335 q = 1) (hb : d357536 q = 1) : d333248 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d357536, d333248, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d357536, d333248, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d331335 q = 1) (hb : d357537 q = 1) : d333249 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d357537, d333249, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d357537, d333249, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d331335 q = 1) (hb : d357538 q = 1) : d333250 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d357538, d333250, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d357538, d333250, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro102896 (p : Pattern) (ha : d331335 p = 1) (hb : d357544 p = 1) : d333256 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d331335 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d43970 q = 1) (hb : d331335 q = 1) : d332556 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d43970, d332556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro102465 q ha hb
    | true =>
      simp only [d43970, d332556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro102468 q ha hb
  have h2 (q : Pattern) (ha : d43971 q = 1) (hb : d331335 q = 1) : d332557 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d43971, d332557, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d43971, d332557, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d331335 q = 1) (hb : d357525 q = 1) : d333237 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d357525, d333237, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d357525, d333237, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d331335 q = 1) (hb : d357526 q = 1) : d333238 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d357526, d333238, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d357526, d333238, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d331335 q = 1) (hb : d357528 q = 1) : d333240 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d357528, d333240, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d357528, d333240, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro102894 q ha hb
  have h6 (q : Pattern) (ha : d331335 q = 1) (hb : d357529 q = 1) : d333241 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d357529, d333241, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d357529, d333241, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d331335 q = 1) (hb : d357530 q = 1) : d333242 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d357530, d333242, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d357530, d333242, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d331335 q = 1) (hb : d357531 q = 1) : d333243 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d357531, d333243, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d357531, d333243, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d331335 q = 1) (hb : d357532 q = 1) : d333244 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d357532, d333244, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d357532, d333244, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d331335 q = 1) (hb : d357539 q = 1) : d333251 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d357539, d333251, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d357539, d333251, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro102895 q ha hb
  have h11 (q : Pattern) (ha : d331335 q = 1) (hb : d357540 q = 1) : d333252 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d357540, d333252, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d357540, d333252, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d331335 q = 1) (hb : d357541 q = 1) : d333253 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d357541, d333253, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d357541, d333253, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d331335 q = 1) (hb : d357542 q = 1) : d333254 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d357542, d333254, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d357542, d333254, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h14 (q : Pattern) (ha : d331335 q = 1) (hb : d357543 q = 1) : d333255 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d357543, d333255, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d357543, d333255, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h15 (q : Pattern) (ha : d331335 q = 1) (hb : d357544 q = 1) : d333256 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d357544, d333256, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d357544, d333256, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro102897 (p : Pattern) (ha : d331335 p = 1) (hb : d357550 p = 1) : d333262 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d331335 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d331335 q = 1) (hb : d357545 q = 1) : d333257 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d357545, d333257, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d357545, d333257, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro102896 q ha hb
  have h2 (q : Pattern) (ha : d331335 q = 1) (hb : d357546 q = 1) : d333258 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d357546, d333258, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d357546, d333258, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d331335 q = 1) (hb : d357547 q = 1) : d333259 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d357547, d333259, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d357547, d333259, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d331335 q = 1) (hb : d357548 q = 1) : d333260 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d357548, d333260, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d357548, d333260, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d331335 q = 1) (hb : d357549 q = 1) : d333261 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d357549, d333261, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d357549, d333261, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d331335 q = 1) (hb : d357550 q = 1) : d333262 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d357550, d333262, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d357550, d333262, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro102898 (p : Pattern) (ha : d331335 p = 1) (hb : d357556 p = 1) : d333298 p = 1 := by
  have h0 (q : Pattern) (ha : d331335 q = 1) (hb : d357467 q = 1) : d333179 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d357467, d333179, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro102881 q ha hb
    | true =>
      simp only [d357467, d333179, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro102885 q ha hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d331335 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d331335 q = 1) (hb : d357494 q = 1) : d333206 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d357494, d333206, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d357494, d333206, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro102889 q ha hb
  have h3 (q : Pattern) (ha : d331335 q = 1) (hb : d357495 q = 1) : d333207 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d357495, d333207, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d357495, d333207, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d331335 q = 1) (hb : d357522 q = 1) : d333234 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d357522, d333234, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d357522, d333234, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro102893 q ha hb
  have h5 (q : Pattern) (ha : d331335 q = 1) (hb : d357523 q = 1) : d333235 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d357523, d333235, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d357523, d333235, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d331335 q = 1) (hb : d357524 q = 1) : d333236 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d357524, d333236, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d357524, d333236, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d331335 q = 1) (hb : d357551 q = 1) : d333263 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d357551, d333263, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d357551, d333263, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro102897 q ha hb
  have h8 (q : Pattern) (ha : d331335 q = 1) (hb : d357552 q = 1) : d333264 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d357552, d333264, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d357552, d333264, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d331335 q = 1) (hb : d357553 q = 1) : d333265 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d357553, d333265, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d357553, d333265, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d331335 q = 1) (hb : d357554 q = 1) : d333266 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d357554, d333266, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d357554, d333266, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d309719 q = 1) (hb : d331335 q = 1) : d333293 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d309719, d333293, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d309719, d333293, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro102877 q ha hb
  have h12 (q : Pattern) (ha : d309720 q = 1) (hb : d331335 q = 1) : d333294 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d309720, d333294, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d309720, d333294, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d309721 q = 1) (hb : d331335 q = 1) : d333295 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d309721, d333295, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d309721, d333295, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d309722 q = 1) (hb : d331335 q = 1) : d333296 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d309722, d333296, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d309722, d333296, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d331335 q = 1) (hb : d357555 q = 1) : d333297 q = 1 := by
    cases bit : q 10250 with
    | false =>
      simp only [d357555, d333297, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d357555, d333297, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d331335 q = 1) (hb : d357556 q = 1) : d333298 q = 1 := by
    cases bit : q 260 with
    | false =>
      simp only [d357556, d333298, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d357556, d333298, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  exact h16 p ha hb
theorem andIntro102899 (p : Pattern) (ha : d331335 p = 1) (hb : d357562 p = 1) : d333304 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d331335 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d331335 q = 1) (hb : d357557 q = 1) : d333299 q = 1 := by
    cases bit : q 259 with
    | false =>
      simp only [d357557, d333299, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro102898 q ha hb
    | true =>
      simp only [d357557, d333299, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d331335 q = 1) (hb : d357558 q = 1) : d333300 q = 1 := by
    cases bit : q 258 with
    | false =>
      simp only [d357558, d333300, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d357558, d333300, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d331335 q = 1) (hb : d357559 q = 1) : d333301 q = 1 := by
    cases bit : q 257 with
    | false =>
      simp only [d357559, d333301, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d357559, d333301, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d331335 q = 1) (hb : d357560 q = 1) : d333302 q = 1 := by
    cases bit : q 256 with
    | false =>
      simp only [d357560, d333302, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d357560, d333302, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d331335 q = 1) (hb : d357561 q = 1) : d333303 q = 1 := by
    cases bit : q 255 with
    | false =>
      simp only [d357561, d333303, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d357561, d333303, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d331335 q = 1) (hb : d357562 q = 1) : d333304 q = 1 := by
    cases bit : q 254 with
    | false =>
      simp only [d357562, d333304, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d357562, d333304, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro102900 (p : Pattern) (ha : d331335 p = 1) (hb : d357568 p = 1) : d333310 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d331335 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d331335 q = 1) (hb : d357563 q = 1) : d333305 q = 1 := by
    cases bit : q 253 with
    | false =>
      simp only [d357563, d333305, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro102899 q ha hb
    | true =>
      simp only [d357563, d333305, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d331335 q = 1) (hb : d357564 q = 1) : d333306 q = 1 := by
    cases bit : q 252 with
    | false =>
      simp only [d357564, d333306, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d357564, d333306, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d331335 q = 1) (hb : d357565 q = 1) : d333307 q = 1 := by
    cases bit : q 251 with
    | false =>
      simp only [d357565, d333307, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d357565, d333307, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d331335 q = 1) (hb : d357566 q = 1) : d333308 q = 1 := by
    cases bit : q 250 with
    | false =>
      simp only [d357566, d333308, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d357566, d333308, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d331335 q = 1) (hb : d357567 q = 1) : d333309 q = 1 := by
    cases bit : q 249 with
    | false =>
      simp only [d357567, d333309, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d357567, d333309, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d331335 q = 1) (hb : d357568 q = 1) : d333310 q = 1 := by
    cases bit : q 245 with
    | false =>
      simp only [d357568, d333310, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d357568, d333310, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro102901 (p : Pattern) (ha : d331335 p = 1) (hb : d357574 p = 1) : d333316 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d331335 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d331335 q = 1) (hb : d357569 q = 1) : d333311 q = 1 := by
    cases bit : q 200 with
    | false =>
      simp only [d357569, d333311, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro102900 q ha hb
    | true =>
      simp only [d357569, d333311, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d331335 q = 1) (hb : d357570 q = 1) : d333312 q = 1 := by
    cases bit : q 199 with
    | false =>
      simp only [d357570, d333312, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d357570, d333312, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d331335 q = 1) (hb : d357571 q = 1) : d333313 q = 1 := by
    cases bit : q 186 with
    | false =>
      simp only [d357571, d333313, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d357571, d333313, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d331335 q = 1) (hb : d357572 q = 1) : d333314 q = 1 := by
    cases bit : q 185 with
    | false =>
      simp only [d357572, d333314, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d357572, d333314, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d331335 q = 1) (hb : d357573 q = 1) : d333315 q = 1 := by
    cases bit : q 184 with
    | false =>
      simp only [d357573, d333315, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d357573, d333315, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d331335 q = 1) (hb : d357574 q = 1) : d333316 q = 1 := by
    cases bit : q 181 with
    | false =>
      simp only [d357574, d333316, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d357574, d333316, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro102902 (p : Pattern) (ha : d331335 p = 1) (hb : d357580 p = 1) : d333322 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d331335 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d331335 q = 1) (hb : d357575 q = 1) : d333317 q = 1 := by
    cases bit : q 177 with
    | false =>
      simp only [d357575, d333317, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro102901 q ha hb
    | true =>
      simp only [d357575, d333317, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d331335 q = 1) (hb : d357576 q = 1) : d333318 q = 1 := by
    cases bit : q 164 with
    | false =>
      simp only [d357576, d333318, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d357576, d333318, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d331335 q = 1) (hb : d357577 q = 1) : d333319 q = 1 := by
    cases bit : q 156 with
    | false =>
      simp only [d357577, d333319, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d357577, d333319, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d331335 q = 1) (hb : d357578 q = 1) : d333320 q = 1 := by
    cases bit : q 155 with
    | false =>
      simp only [d357578, d333320, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d357578, d333320, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d331335 q = 1) (hb : d357579 q = 1) : d333321 q = 1 := by
    cases bit : q 134 with
    | false =>
      simp only [d357579, d333321, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d357579, d333321, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d331335 q = 1) (hb : d357580 q = 1) : d333322 q = 1 := by
    cases bit : q 133 with
    | false =>
      simp only [d357580, d333322, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d357580, d333322, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro102903 (p : Pattern) (ha : d331335 p = 1) (hb : d357586 p = 1) : d333328 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d331335 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d331335 q = 1) (hb : d357581 q = 1) : d333323 q = 1 := by
    cases bit : q 120 with
    | false =>
      simp only [d357581, d333323, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro102902 q ha hb
    | true =>
      simp only [d357581, d333323, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d331335 q = 1) (hb : d357582 q = 1) : d333324 q = 1 := by
    cases bit : q 118 with
    | false =>
      simp only [d357582, d333324, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d357582, d333324, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d331335 q = 1) (hb : d357583 q = 1) : d333325 q = 1 := by
    cases bit : q 114 with
    | false =>
      simp only [d357583, d333325, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d357583, d333325, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d331335 q = 1) (hb : d357584 q = 1) : d333326 q = 1 := by
    cases bit : q 111 with
    | false =>
      simp only [d357584, d333326, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d357584, d333326, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d331335 q = 1) (hb : d357585 q = 1) : d333327 q = 1 := by
    cases bit : q 98 with
    | false =>
      simp only [d357585, d333327, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d357585, d333327, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d331335 q = 1) (hb : d357586 q = 1) : d333328 q = 1 := by
    cases bit : q 97 with
    | false =>
      simp only [d357586, d333328, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d357586, d333328, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro102904 (p : Pattern) (ha : d331335 p = 1) (hb : d357592 p = 1) : d333334 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d331335 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d331335 q = 1) (hb : d357587 q = 1) : d333329 q = 1 := by
    cases bit : q 94 with
    | false =>
      simp only [d357587, d333329, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro102903 q ha hb
    | true =>
      simp only [d357587, d333329, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d331335 q = 1) (hb : d357588 q = 1) : d333330 q = 1 := by
    cases bit : q 76 with
    | false =>
      simp only [d357588, d333330, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d357588, d333330, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d331335 q = 1) (hb : d357589 q = 1) : d333331 q = 1 := by
    cases bit : q 67 with
    | false =>
      simp only [d357589, d333331, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d357589, d333331, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d331335 q = 1) (hb : d357590 q = 1) : d333332 q = 1 := by
    cases bit : q 52 with
    | false =>
      simp only [d357590, d333332, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d357590, d333332, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d331335 q = 1) (hb : d357591 q = 1) : d333333 q = 1 := by
    cases bit : q 47 with
    | false =>
      simp only [d357591, d333333, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d357591, d333333, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d331335 q = 1) (hb : d357592 q = 1) : d333334 q = 1 := by
    cases bit : q 46 with
    | false =>
      simp only [d357592, d333334, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d357592, d333334, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro102905 (p : Pattern) (ha : d331335 p = 1) (hb : d357598 p = 1) : d333340 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d331335 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d331335 q = 1) (hb : d357593 q = 1) : d333335 q = 1 := by
    cases bit : q 45 with
    | false =>
      simp only [d357593, d333335, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro102904 q ha hb
    | true =>
      simp only [d357593, d333335, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d331335 q = 1) (hb : d357594 q = 1) : d333336 q = 1 := by
    cases bit : q 30 with
    | false =>
      simp only [d357594, d333336, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d357594, d333336, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d331335 q = 1) (hb : d357595 q = 1) : d333337 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d357595, d333337, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d357595, d333337, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d331335 q = 1) (hb : d357596 q = 1) : d333338 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d357596, d333338, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d357596, d333338, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d331335 q = 1) (hb : d357597 q = 1) : d333339 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d357597, d333339, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d357597, d333339, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d331335 q = 1) (hb : d357598 q = 1) : d333340 q = 1 := by
    cases bit : q 25 with
    | false =>
      simp only [d357598, d333340, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d357598, d333340, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro102906 (p : Pattern) (ha : d267996 p = 1) (hb : d331425 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d267946 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d267952 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d267985 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d267866 q = 1) (hb : d331361 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d267866, d331361, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro102530 q ha hb
    | true =>
      simp only [d267866, d331361, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5 q hb ha
  have h5 (q : Pattern) (ha : d267986 q = 1) (hb : d331421 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d267986, d331421, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d267986, d331421, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d267992 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d267993 q = 1) (hb : d331422 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d267993, d331422, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d267993, d331422, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d267994 q = 1) (hb : d331423 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d267994, d331423, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d267994, d331423, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d267995 q = 1) (hb : d331424 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d267995, d331424, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d267995, d331424, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d267996 q = 1) (hb : d331425 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d267996, d331425, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d267996, d331425, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro102907 (p : Pattern) (ha : d268015 p = 1) (hb : d331432 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d267946 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d267952 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d267985 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d267866 q = 1) (hb : d331361 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d267866, d331361, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro102530 q ha hb
    | true =>
      simp only [d267866, d331361, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5 q hb ha
  have h4 (q : Pattern) (ha : d267986 q = 1) (hb : d331421 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d267986, d331421, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d267986, d331421, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d267992 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d267993 q = 1) (hb : d331422 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d267993, d331422, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d267993, d331422, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d267994 q = 1) (hb : d331423 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d267994, d331423, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d267994, d331423, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d267995 q = 1) (hb : d331424 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d267995, d331424, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d267995, d331424, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d268001 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d268005 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d268007 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d267873 q = 1) (hb : d331368 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d267873, d331368, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro102532 q ha hb
    | true =>
      simp only [d267873, d331368, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7 q hb ha
  have h13 (q : Pattern) (ha : d268008 q = 1) (hb : d331428 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d268008, d331428, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
    | true =>
      simp only [d268008, d331428, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d268011 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d268012 q = 1) (hb : d331429 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d268012, d331429, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d268012, d331429, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d268013 q = 1) (hb : d331430 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d268013, d331430, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
    | true =>
      simp only [d268013, d331430, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d268014 q = 1) (hb : d331431 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d268014, d331431, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
    | true =>
      simp only [d268014, d331431, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d268015 q = 1) (hb : d331432 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d268015, d331432, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d268015, d331432, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro102908 (p : Pattern) (ha : d268024 p = 1) (hb : d333130 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d268007 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d267873 q = 1) (hb : d331368 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d267873, d331368, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro102532 q ha hb
    | true =>
      simp only [d267873, d331368, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7 q hb ha
  have h3 (q : Pattern) (ha : d268008 q = 1) (hb : d331428 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d268008, d331428, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d268008, d331428, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d268011 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d268012 q = 1) (hb : d331429 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d268012, d331429, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d268012, d331429, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d268022 q = 1) (hb : d331430 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d268022, d331430, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d268022, d331430, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d268023 q = 1) (hb : d331431 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d268023, d331431, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d268023, d331431, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d268024 q = 1) (hb : d333130 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d268024, d333130, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d268024, d333130, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro102909 (p : Pattern) (ha : d268064 p = 1) (hb : d333140 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d268053 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d267909 q = 1) (hb : d331404 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d267909, d331404, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro102537 q ha hb
    | true =>
      simp only [d267909, d331404, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12 q hb ha
  have h3 (q : Pattern) (ha : d268054 q = 1) (hb : d333136 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d268054, d333136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d268054, d333136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d268060 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d268061 q = 1) (hb : d333137 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d268061, d333137, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d268061, d333137, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d268062 q = 1) (hb : d333138 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d268062, d333138, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d268062, d333138, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d268063 q = 1) (hb : d333139 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d268063, d333139, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d268063, d333139, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d268064 q = 1) (hb : d333140 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d268064, d333140, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d268064, d333140, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro102910 (p : Pattern) (ha : d268070 p = 1) (hb : d333146 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d267940 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d268016 q = 1) (hb : d331433 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d268016, d331433, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro102906 q ha hb
    | true =>
      simp only [d268016, d331433, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro102907 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d268018 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d268019 q = 1) (hb : d331434 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d268019, d331434, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d268019, d331434, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d268020 q = 1) (hb : d333128 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d268020, d333128, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d268020, d333128, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d268021 q = 1) (hb : d333129 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d268021, d333129, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d268021, d333129, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d268025 q = 1) (hb : d333131 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d268025, d333131, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d268025, d333131, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro102908 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d52173 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d268026 q = 1) (hb : d333132 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d268026, d333132, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d268026, d333132, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d268027 q = 1) (hb : d333133 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d268027, d333133, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d268027, d333133, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h11 (q : Pattern) (ha : d268028 q = 1) (hb : d333134 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d268028, d333134, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d268028, d333134, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h12 (q : Pattern) (ha : d268029 q = 1) (hb : d333135 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d268029, d333135, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d268029, d333135, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d268065 q = 1) (hb : d333141 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d268065, d333141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d268065, d333141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro102909 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d52210 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d268066 q = 1) (hb : d333142 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d268066, d333142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d268066, d333142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d268067 q = 1) (hb : d333143 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d268067, d333143, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d268067, d333143, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h17 (q : Pattern) (ha : d268068 q = 1) (hb : d333144 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d268068, d333144, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d268068, d333144, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h18 (q : Pattern) (ha : d268069 q = 1) (hb : d333145 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d268069, d333145, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d268069, d333145, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h19 (q : Pattern) (ha : d268070 q = 1) (hb : d333146 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d268070, d333146, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d268070, d333146, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro102911 (p : Pattern) (ha : d268076 p = 1) (hb : d333152 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d51951 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d53648 q = 1) (hb : d267921 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d53648, d267921, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d53648, d267921, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro68632 q ha hb
  have h3 (q : Pattern) (ha : d53649 q = 1) (hb : d267922 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d53649, d267922, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d53649, d267922, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d53650 q = 1) (hb : d267923 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d53650, d267923, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d53650, d267923, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d53651 q = 1) (hb : d267924 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d53651, d267924, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d53651, d267924, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d53652 q = 1) (hb : d267925 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d53652, d267925, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53652, d267925, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d268071 q = 1) (hb : d333147 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d268071, d333147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d268071, d333147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro102910 q ha hb
  have h8 (q : Pattern) (ha : d268072 q = 1) (hb : d333148 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d268072, d333148, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d268072, d333148, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d268073 q = 1) (hb : d333149 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d268073, d333149, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d268073, d333149, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d268074 q = 1) (hb : d333150 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d268074, d333150, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d268074, d333150, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d268075 q = 1) (hb : d333151 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d268075, d333151, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d268075, d333151, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d268076 q = 1) (hb : d333152 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d268076, d333152, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
    | true =>
      simp only [d268076, d333152, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  exact h12 p ha hb
theorem andIntro102912 (p : Pattern) (ha : d268184 p = 1) (hb : d331595 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d268120 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d268129 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d268173 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d268094 q = 1) (hb : d331590 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d268094, d331590, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro102568 q ha hb
    | true =>
      simp only [d268094, d331590, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro102569 q ha hb
  have h5 (q : Pattern) (ha : d268174 q = 1) (hb : d331591 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d268174, d331591, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d268174, d331591, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d268180 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d268181 q = 1) (hb : d331592 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d268181, d331592, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d268181, d331592, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d268182 q = 1) (hb : d331593 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d268182, d331593, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d268182, d331593, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d268183 q = 1) (hb : d331594 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d268183, d331594, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d268183, d331594, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d268184 q = 1) (hb : d331595 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d268184, d331595, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d268184, d331595, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro102913 (p : Pattern) (ha : d268205 p = 1) (hb : d331605 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d268120 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d268129 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d268173 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d268094 q = 1) (hb : d331590 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d268094, d331590, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro102568 q ha hb
    | true =>
      simp only [d268094, d331590, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro102569 q ha hb
  have h4 (q : Pattern) (ha : d268174 q = 1) (hb : d331591 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d268174, d331591, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d268174, d331591, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d268180 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d268181 q = 1) (hb : d331592 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d268181, d331592, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d268181, d331592, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d268182 q = 1) (hb : d331593 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d268182, d331593, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d268182, d331593, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d268183 q = 1) (hb : d331594 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d268183, d331594, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d268183, d331594, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d268190 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d268195 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d268197 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d268104 q = 1) (hb : d331600 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d268104, d331600, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro102571 q ha hb
    | true =>
      simp only [d268104, d331600, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro102572 q ha hb
  have h13 (q : Pattern) (ha : d268198 q = 1) (hb : d331601 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d268198, d331601, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
    | true =>
      simp only [d268198, d331601, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d268201 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d268202 q = 1) (hb : d331602 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d268202, d331602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d268202, d331602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d268203 q = 1) (hb : d331603 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d268203, d331603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
    | true =>
      simp only [d268203, d331603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d268204 q = 1) (hb : d331604 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d268204, d331604, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
    | true =>
      simp only [d268204, d331604, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d268205 q = 1) (hb : d331605 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d268205, d331605, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d268205, d331605, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro102914 (p : Pattern) (ha : d268225 p = 1) (hb : d333155 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d268197 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d268104 q = 1) (hb : d331600 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d268104, d331600, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro102571 q ha hb
    | true =>
      simp only [d268104, d331600, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro102572 q ha hb
  have h3 (q : Pattern) (ha : d268198 q = 1) (hb : d331601 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d268198, d331601, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d268198, d331601, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d268201 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d268202 q = 1) (hb : d331602 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d268202, d331602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d268202, d331602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d268223 q = 1) (hb : d331603 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d268223, d331603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d268223, d331603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d268224 q = 1) (hb : d331604 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d268224, d331604, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d268224, d331604, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d268225 q = 1) (hb : d333155 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d268225, d333155, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d268225, d333155, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro102915 (p : Pattern) (ha : d268293 p = 1) (hb : d333166 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d268277 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d268282 q = 1) (hb : d333161 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d268282, d333161, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro102605 q ha hb
    | true =>
      simp only [d268282, d333161, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro102608 q ha hb
  have h3 (q : Pattern) (ha : d268283 q = 1) (hb : d333162 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d268283, d333162, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d268283, d333162, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d268289 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d268290 q = 1) (hb : d333163 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d268290, d333163, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d268290, d333163, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d268291 q = 1) (hb : d333164 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d268291, d333164, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d268291, d333164, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d268292 q = 1) (hb : d333165 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d268292, d333165, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d268292, d333165, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d268293 q = 1) (hb : d333166 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d268293, d333166, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d268293, d333166, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro102916 (p : Pattern) (ha : d268306 p = 1) (hb : d333172 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d268112 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d268206 q = 1) (hb : d331606 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d268206, d331606, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro102912 q ha hb
    | true =>
      simp only [d268206, d331606, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro102913 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d268219 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d268220 q = 1) (hb : d331607 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d268220, d331607, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d268220, d331607, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d268221 q = 1) (hb : d333153 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d268221, d333153, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d268221, d333153, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d268222 q = 1) (hb : d333154 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d268222, d333154, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d268222, d333154, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d268226 q = 1) (hb : d333156 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d268226, d333156, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d268226, d333156, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro102914 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d268228 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d268229 q = 1) (hb : d333157 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d268229, d333157, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d268229, d333157, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d268230 q = 1) (hb : d333158 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d268230, d333158, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d268230, d333158, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h11 (q : Pattern) (ha : d268231 q = 1) (hb : d333159 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d268231, d333159, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d268231, d333159, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h12 (q : Pattern) (ha : d268232 q = 1) (hb : d333160 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d268232, d333160, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d268232, d333160, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d268294 q = 1) (hb : d333167 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d268294, d333167, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d268294, d333167, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro102915 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d268301 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d268302 q = 1) (hb : d333168 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d268302, d333168, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d268302, d333168, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d268303 q = 1) (hb : d333169 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d268303, d333169, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d268303, d333169, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h17 (q : Pattern) (ha : d268304 q = 1) (hb : d333170 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d268304, d333170, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d268304, d333170, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h18 (q : Pattern) (ha : d268305 q = 1) (hb : d333171 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d268305, d333171, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d268305, d333171, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h19 (q : Pattern) (ha : d268306 q = 1) (hb : d333172 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d268306, d333172, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d268306, d333172, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro102917 (p : Pattern) (ha : d268312 p = 1) (hb : d333178 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d268307 q = 1) (hb : d333173 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d268307, d333173, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d268307, d333173, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro102916 q ha hb
  have h2 (q : Pattern) (ha : d268308 q = 1) (hb : d333174 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d268308, d333174, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d268308, d333174, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d268309 q = 1) (hb : d333175 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d268309, d333175, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d268309, d333175, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d268310 q = 1) (hb : d333176 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d268310, d333176, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d268310, d333176, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d268311 q = 1) (hb : d333177 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d268311, d333177, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d268311, d333177, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d268312 q = 1) (hb : d333178 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d268312, d333178, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d268312, d333178, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro102918 (p : Pattern) (ha : d268439 p = 1) (hb : d331845 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d268375 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d268384 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d268428 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d268349 q = 1) (hb : d331840 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d268349, d331840, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro102618 q ha hb
    | true =>
      simp only [d268349, d331840, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro102619 q ha hb
  have h5 (q : Pattern) (ha : d268429 q = 1) (hb : d331841 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d268429, d331841, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d268429, d331841, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d268435 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d268436 q = 1) (hb : d331842 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d268436, d331842, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d268436, d331842, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d268437 q = 1) (hb : d331843 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d268437, d331843, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d268437, d331843, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d268438 q = 1) (hb : d331844 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d268438, d331844, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d268438, d331844, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d268439 q = 1) (hb : d331845 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d268439, d331845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d268439, d331845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro102919 (p : Pattern) (ha : d268460 p = 1) (hb : d331855 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d268375 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d268384 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d268428 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d268349 q = 1) (hb : d331840 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d268349, d331840, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro102618 q ha hb
    | true =>
      simp only [d268349, d331840, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro102619 q ha hb
  have h4 (q : Pattern) (ha : d268429 q = 1) (hb : d331841 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d268429, d331841, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d268429, d331841, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d268435 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d268436 q = 1) (hb : d331842 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d268436, d331842, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d268436, d331842, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d268437 q = 1) (hb : d331843 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d268437, d331843, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d268437, d331843, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d268438 q = 1) (hb : d331844 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d268438, d331844, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d268438, d331844, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d268445 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d268450 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d268452 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d268359 q = 1) (hb : d331850 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d268359, d331850, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro102621 q ha hb
    | true =>
      simp only [d268359, d331850, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro102622 q ha hb
  have h13 (q : Pattern) (ha : d268453 q = 1) (hb : d331851 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d268453, d331851, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
    | true =>
      simp only [d268453, d331851, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d268456 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d268457 q = 1) (hb : d331852 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d268457, d331852, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d268457, d331852, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d268458 q = 1) (hb : d331853 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d268458, d331853, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
    | true =>
      simp only [d268458, d331853, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d268459 q = 1) (hb : d331854 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d268459, d331854, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
    | true =>
      simp only [d268459, d331854, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d268460 q = 1) (hb : d331855 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d268460, d331855, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d268460, d331855, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro102920 (p : Pattern) (ha : d268480 p = 1) (hb : d333182 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d268452 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d268359 q = 1) (hb : d331850 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d268359, d331850, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro102621 q ha hb
    | true =>
      simp only [d268359, d331850, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro102622 q ha hb
  have h3 (q : Pattern) (ha : d268453 q = 1) (hb : d331851 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d268453, d331851, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d268453, d331851, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d268456 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d268457 q = 1) (hb : d331852 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d268457, d331852, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d268457, d331852, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d268478 q = 1) (hb : d331853 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d268478, d331853, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d268478, d331853, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d268479 q = 1) (hb : d331854 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d268479, d331854, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d268479, d331854, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d268480 q = 1) (hb : d333182 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d268480, d333182, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d268480, d333182, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro102921 (p : Pattern) (ha : d268565 p = 1) (hb : d333193 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d268549 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d268554 q = 1) (hb : d333188 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d268554, d333188, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro102658 q ha hb
    | true =>
      simp only [d268554, d333188, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro102661 q ha hb
  have h3 (q : Pattern) (ha : d268555 q = 1) (hb : d333189 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d268555, d333189, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d268555, d333189, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d268561 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d268562 q = 1) (hb : d333190 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d268562, d333190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d268562, d333190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d268563 q = 1) (hb : d333191 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d268563, d333191, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d268563, d333191, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d268564 q = 1) (hb : d333192 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d268564, d333192, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d268564, d333192, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d268565 q = 1) (hb : d333193 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d268565, d333193, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d268565, d333193, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro102922 (p : Pattern) (ha : d268578 p = 1) (hb : d333199 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d268367 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d268461 q = 1) (hb : d331856 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d268461, d331856, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro102918 q ha hb
    | true =>
      simp only [d268461, d331856, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro102919 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d268474 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d268475 q = 1) (hb : d331857 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d268475, d331857, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d268475, d331857, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d268476 q = 1) (hb : d333180 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d268476, d333180, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d268476, d333180, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d268477 q = 1) (hb : d333181 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d268477, d333181, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d268477, d333181, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d268481 q = 1) (hb : d333183 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d268481, d333183, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d268481, d333183, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro102920 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d268483 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d268484 q = 1) (hb : d333184 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d268484, d333184, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d268484, d333184, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d268485 q = 1) (hb : d333185 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d268485, d333185, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d268485, d333185, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h11 (q : Pattern) (ha : d268486 q = 1) (hb : d333186 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d268486, d333186, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d268486, d333186, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h12 (q : Pattern) (ha : d268487 q = 1) (hb : d333187 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d268487, d333187, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d268487, d333187, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d268566 q = 1) (hb : d333194 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d268566, d333194, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d268566, d333194, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro102921 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d268573 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d268574 q = 1) (hb : d333195 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d268574, d333195, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d268574, d333195, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d268575 q = 1) (hb : d333196 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d268575, d333196, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d268575, d333196, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h17 (q : Pattern) (ha : d268576 q = 1) (hb : d333197 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d268576, d333197, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d268576, d333197, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h18 (q : Pattern) (ha : d268577 q = 1) (hb : d333198 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d268577, d333198, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d268577, d333198, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h19 (q : Pattern) (ha : d268578 q = 1) (hb : d333199 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d268578, d333199, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d268578, d333199, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro102923 (p : Pattern) (ha : d268584 p = 1) (hb : d333205 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d268579 q = 1) (hb : d333200 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d268579, d333200, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d268579, d333200, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro102922 q ha hb
  have h2 (q : Pattern) (ha : d268580 q = 1) (hb : d333201 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d268580, d333201, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d268580, d333201, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d268581 q = 1) (hb : d333202 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d268581, d333202, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d268581, d333202, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d268582 q = 1) (hb : d333203 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d268582, d333203, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d268582, d333203, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d268583 q = 1) (hb : d333204 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d268583, d333204, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d268583, d333204, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d268584 q = 1) (hb : d333205 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d268584, d333205, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d268584, d333205, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro102924 (p : Pattern) (ha : d268774 p = 1) (hb : d332173 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d268695 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d268704 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d268754 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d268669 q = 1) (hb : d332168 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d268669, d332168, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro102676 q ha hb
    | true =>
      simp only [d268669, d332168, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro102677 q ha hb
  have h5 (q : Pattern) (ha : d268755 q = 1) (hb : d332169 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d268755, d332169, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d268755, d332169, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d268770 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d268771 q = 1) (hb : d332170 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d268771, d332170, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d268771, d332170, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d268772 q = 1) (hb : d332171 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d268772, d332171, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d268772, d332171, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d268773 q = 1) (hb : d332172 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d268773, d332172, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d268773, d332172, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d268774 q = 1) (hb : d332173 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d268774, d332173, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d268774, d332173, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro102925 (p : Pattern) (ha : d268795 p = 1) (hb : d332183 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d268695 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d268704 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d268754 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d268669 q = 1) (hb : d332168 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d268669, d332168, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro102676 q ha hb
    | true =>
      simp only [d268669, d332168, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro102677 q ha hb
  have h4 (q : Pattern) (ha : d268755 q = 1) (hb : d332169 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d268755, d332169, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d268755, d332169, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d268770 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d268771 q = 1) (hb : d332170 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d268771, d332170, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d268771, d332170, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d268772 q = 1) (hb : d332171 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d268772, d332171, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d268772, d332171, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d268773 q = 1) (hb : d332172 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d268773, d332172, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d268773, d332172, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d268780 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d268785 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d268787 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d268679 q = 1) (hb : d332178 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d268679, d332178, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro102679 q ha hb
    | true =>
      simp only [d268679, d332178, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro102680 q ha hb
  have h13 (q : Pattern) (ha : d268788 q = 1) (hb : d332179 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d268788, d332179, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
    | true =>
      simp only [d268788, d332179, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d268791 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d268792 q = 1) (hb : d332180 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d268792, d332180, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d268792, d332180, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d268793 q = 1) (hb : d332181 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d268793, d332181, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
    | true =>
      simp only [d268793, d332181, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d268794 q = 1) (hb : d332182 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d268794, d332182, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
    | true =>
      simp only [d268794, d332182, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d268795 q = 1) (hb : d332183 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d268795, d332183, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d268795, d332183, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro102926 (p : Pattern) (ha : d268815 p = 1) (hb : d333210 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d268787 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d268679 q = 1) (hb : d332178 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d268679, d332178, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro102679 q ha hb
    | true =>
      simp only [d268679, d332178, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro102680 q ha hb
  have h3 (q : Pattern) (ha : d268788 q = 1) (hb : d332179 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d268788, d332179, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d268788, d332179, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d268791 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d268792 q = 1) (hb : d332180 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d268792, d332180, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d268792, d332180, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d268813 q = 1) (hb : d332181 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d268813, d332181, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d268813, d332181, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d268814 q = 1) (hb : d332182 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d268814, d332182, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d268814, d332182, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d268815 q = 1) (hb : d333210 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d268815, d333210, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d268815, d333210, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro102927 (p : Pattern) (ha : d268936 p = 1) (hb : d333221 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d268911 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d268916 q = 1) (hb : d333216 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d268916, d333216, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro102718 q ha hb
    | true =>
      simp only [d268916, d333216, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro102723 q ha hb
  have h3 (q : Pattern) (ha : d268917 q = 1) (hb : d333217 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d268917, d333217, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d268917, d333217, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d268932 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d268933 q = 1) (hb : d333218 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d268933, d333218, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d268933, d333218, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d268934 q = 1) (hb : d333219 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d268934, d333219, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d268934, d333219, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d268935 q = 1) (hb : d333220 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d268935, d333220, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d268935, d333220, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d268936 q = 1) (hb : d333221 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d268936, d333221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d268936, d333221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro102928 (p : Pattern) (ha : d268949 p = 1) (hb : d333227 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d268687 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d268796 q = 1) (hb : d332184 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d268796, d332184, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro102924 q ha hb
    | true =>
      simp only [d268796, d332184, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro102925 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d268809 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d268810 q = 1) (hb : d332185 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d268810, d332185, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d268810, d332185, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d268811 q = 1) (hb : d333208 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d268811, d333208, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d268811, d333208, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d268812 q = 1) (hb : d333209 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d268812, d333209, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d268812, d333209, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d268816 q = 1) (hb : d333211 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d268816, d333211, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d268816, d333211, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro102926 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d268818 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d268819 q = 1) (hb : d333212 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d268819, d333212, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d268819, d333212, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d268820 q = 1) (hb : d333213 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d268820, d333213, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d268820, d333213, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h11 (q : Pattern) (ha : d268821 q = 1) (hb : d333214 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d268821, d333214, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d268821, d333214, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h12 (q : Pattern) (ha : d268822 q = 1) (hb : d333215 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d268822, d333215, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d268822, d333215, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d268937 q = 1) (hb : d333222 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d268937, d333222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d268937, d333222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro102927 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d268944 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d268945 q = 1) (hb : d333223 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d268945, d333223, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d268945, d333223, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d268946 q = 1) (hb : d333224 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d268946, d333224, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d268946, d333224, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h17 (q : Pattern) (ha : d268947 q = 1) (hb : d333225 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d268947, d333225, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d268947, d333225, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h18 (q : Pattern) (ha : d268948 q = 1) (hb : d333226 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d268948, d333226, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d268948, d333226, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h19 (q : Pattern) (ha : d268949 q = 1) (hb : d333227 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d268949, d333227, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d268949, d333227, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro102929 (p : Pattern) (ha : d268955 p = 1) (hb : d333233 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d268950 q = 1) (hb : d333228 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d268950, d333228, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d268950, d333228, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro102928 q ha hb
  have h2 (q : Pattern) (ha : d268951 q = 1) (hb : d333229 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d268951, d333229, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d268951, d333229, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d268952 q = 1) (hb : d333230 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d268952, d333230, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d268952, d333230, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d268953 q = 1) (hb : d333231 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d268953, d333231, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d268953, d333231, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d268954 q = 1) (hb : d333232 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d268954, d333232, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d268954, d333232, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d268955 q = 1) (hb : d333233 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d268955, d333233, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d268955, d333233, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro102930 (p : Pattern) (ha : d269204 p = 1) (hb : d332545 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d269112 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d269121 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d269171 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d269086 q = 1) (hb : d332540 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d269086, d332540, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro102743 q ha hb
    | true =>
      simp only [d269086, d332540, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro102744 q ha hb
  have h5 (q : Pattern) (ha : d269172 q = 1) (hb : d332541 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d269172, d332541, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d269172, d332541, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d269200 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d269201 q = 1) (hb : d332542 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d269201, d332542, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d269201, d332542, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d269202 q = 1) (hb : d332543 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d269202, d332543, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d269202, d332543, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d269203 q = 1) (hb : d332544 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d269203, d332544, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d269203, d332544, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d269204 q = 1) (hb : d332545 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d269204, d332545, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d269204, d332545, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro102931 (p : Pattern) (ha : d269226 p = 1) (hb : d332555 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d269112 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d269121 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d269171 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d269086 q = 1) (hb : d332540 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d269086, d332540, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro102743 q ha hb
    | true =>
      simp only [d269086, d332540, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro102744 q ha hb
  have h4 (q : Pattern) (ha : d269172 q = 1) (hb : d332541 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d269172, d332541, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d269172, d332541, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d269200 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d269201 q = 1) (hb : d332542 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d269201, d332542, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d269201, d332542, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d269202 q = 1) (hb : d332543 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d269202, d332543, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d269202, d332543, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d269203 q = 1) (hb : d332544 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d269203, d332544, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d269203, d332544, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d269210 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d269215 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d269218 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d269096 q = 1) (hb : d332550 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d269096, d332550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro102746 q ha hb
    | true =>
      simp only [d269096, d332550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro102747 q ha hb
  have h13 (q : Pattern) (ha : d269219 q = 1) (hb : d332551 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d269219, d332551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
    | true =>
      simp only [d269219, d332551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d269222 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d269223 q = 1) (hb : d332552 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d269223, d332552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d269223, d332552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d269224 q = 1) (hb : d332553 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d269224, d332553, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
    | true =>
      simp only [d269224, d332553, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d269225 q = 1) (hb : d332554 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d269225, d332554, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
    | true =>
      simp only [d269225, d332554, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d269226 q = 1) (hb : d332555 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d269226, d332555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d269226, d332555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro102932 (p : Pattern) (ha : d269251 p = 1) (hb : d333239 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d269218 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d269096 q = 1) (hb : d332550 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d269096, d332550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro102746 q ha hb
    | true =>
      simp only [d269096, d332550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro102747 q ha hb
  have h3 (q : Pattern) (ha : d269219 q = 1) (hb : d332551 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d269219, d332551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d269219, d332551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d269222 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d269223 q = 1) (hb : d332552 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d269223, d332552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d269223, d332552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d269249 q = 1) (hb : d332553 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d269249, d332553, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d269249, d332553, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d269250 q = 1) (hb : d332554 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d269250, d332554, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d269250, d332554, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d269251 q = 1) (hb : d333239 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d269251, d333239, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d269251, d333239, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro102933 (p : Pattern) (ha : d269360 p = 1) (hb : d332753 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d269313 q = 1) (hb : d332738 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d269313, d332738, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro102782 q ha hb
    | true =>
      simp only [d269313, d332738, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro102784 q ha hb
  have h2 (q : Pattern) (ha : d269314 q = 1) (hb : d332739 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d269314, d332739, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d269314, d332739, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d269315 q = 1) (hb : d332740 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d269315, d332740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d269315, d332740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d269327 q = 1) (hb : d332743 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d269327, d332743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro102784 q ha hb
    | true =>
      simp only [d269327, d332743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro102785 q ha hb
  have h5 (q : Pattern) (ha : d269328 q = 1) (hb : d332744 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d269328, d332744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d269328, d332744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d269329 q = 1) (hb : d332745 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d269329, d332745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d269329, d332745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d269330 q = 1) (hb : d332746 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d269330, d332746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d269330, d332746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d269346 q = 1) (hb : d332743 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d269346, d332743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro102784 q ha hb
    | true =>
      simp only [d269346, d332743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro102789 q ha hb
  have h9 (q : Pattern) (ha : d269347 q = 1) (hb : d332744 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d269347, d332744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d269347, d332744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d269348 q = 1) (hb : d332745 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d269348, d332745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d269348, d332745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d269349 q = 1) (hb : d332751 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d269349, d332751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d269349, d332751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d269359 q = 1) (hb : d332752 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d269359, d332752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d269359, d332752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d269360 q = 1) (hb : d332753 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d269360, d332753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d269360, d332753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h13 p ha hb
theorem andIntro102934 (p : Pattern) (ha : d269366 p = 1) (hb : d332767 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d269361 q = 1) (hb : d332754 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d269361, d332754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro102933 q ha hb
    | true =>
      simp only [d269361, d332754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d269362 q = 1) (hb : d332755 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d269362, d332755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d269362, d332755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d269352 q = 1) (hb : d332762 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d269352, d332762, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro102790 q ha hb
    | true =>
      simp only [d269352, d332762, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d269353 q = 1) (hb : d332763 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d269353, d332763, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d269353, d332763, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d269363 q = 1) (hb : d332764 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d269363, d332764, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d269363, d332764, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d269364 q = 1) (hb : d332765 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d269364, d332765, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d269364, d332765, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d269365 q = 1) (hb : d332766 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d269365, d332766, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d269365, d332766, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d269366 q = 1) (hb : d332767 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d269366, d332767, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d269366, d332767, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro102935 (p : Pattern) (ha : d269402 p = 1) (hb : d333250 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d269358 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d269371 q = 1) (hb : d333245 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d269371, d333245, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro102934 q ha hb
    | true =>
      simp only [d269371, d333245, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro102797 q ha hb
  have h3 (q : Pattern) (ha : d269372 q = 1) (hb : d333246 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d269372, d333246, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d269372, d333246, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d269398 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d269399 q = 1) (hb : d333247 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d269399, d333247, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d269399, d333247, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d269400 q = 1) (hb : d333248 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d269400, d333248, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d269400, d333248, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d269401 q = 1) (hb : d333249 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d269401, d333249, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d269401, d333249, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d269402 q = 1) (hb : d333250 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d269402, d333250, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d269402, d333250, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro102936 (p : Pattern) (ha : d269415 p = 1) (hb : d333256 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d269104 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d269227 q = 1) (hb : d332556 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d269227, d332556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro102930 q ha hb
    | true =>
      simp only [d269227, d332556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro102931 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d269245 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d269246 q = 1) (hb : d332557 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d269246, d332557, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d269246, d332557, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d269247 q = 1) (hb : d333237 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d269247, d333237, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d269247, d333237, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d269248 q = 1) (hb : d333238 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d269248, d333238, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d269248, d333238, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d269252 q = 1) (hb : d333240 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d269252, d333240, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d269252, d333240, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro102932 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d269254 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d269255 q = 1) (hb : d333241 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d269255, d333241, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d269255, d333241, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d269256 q = 1) (hb : d333242 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d269256, d333242, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d269256, d333242, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h11 (q : Pattern) (ha : d269257 q = 1) (hb : d333243 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d269257, d333243, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d269257, d333243, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h12 (q : Pattern) (ha : d269258 q = 1) (hb : d333244 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d269258, d333244, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d269258, d333244, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d269403 q = 1) (hb : d333251 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d269403, d333251, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d269403, d333251, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro102935 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d269410 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d269411 q = 1) (hb : d333252 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d269411, d333252, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d269411, d333252, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d269412 q = 1) (hb : d333253 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d269412, d333253, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d269412, d333253, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h17 (q : Pattern) (ha : d269413 q = 1) (hb : d333254 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d269413, d333254, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d269413, d333254, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h18 (q : Pattern) (ha : d269414 q = 1) (hb : d333255 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d269414, d333255, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d269414, d333255, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h19 (q : Pattern) (ha : d269415 q = 1) (hb : d333256 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d269415, d333256, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d269415, d333256, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro102937 (p : Pattern) (ha : d269421 p = 1) (hb : d333262 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d269416 q = 1) (hb : d333257 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d269416, d333257, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d269416, d333257, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro102936 q ha hb
  have h2 (q : Pattern) (ha : d269417 q = 1) (hb : d333258 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d269417, d333258, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d269417, d333258, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d269418 q = 1) (hb : d333259 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d269418, d333259, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d269418, d333259, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d269419 q = 1) (hb : d333260 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d269419, d333260, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d269419, d333260, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d269420 q = 1) (hb : d333261 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d269420, d333261, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d269420, d333261, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d269421 q = 1) (hb : d333262 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d269421, d333262, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d269421, d333262, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro102938 (p : Pattern) (ha : d269633 p = 1) (hb : d332878 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d269563 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d269572 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d269600 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d269537 q = 1) (hb : d332873 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d269537, d332873, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro102813 q ha hb
    | true =>
      simp only [d269537, d332873, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro102814 q ha hb
  have h5 (q : Pattern) (ha : d269601 q = 1) (hb : d332874 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d269601, d332874, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d269601, d332874, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d269629 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d269630 q = 1) (hb : d332875 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d269630, d332875, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d269630, d332875, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d269631 q = 1) (hb : d332876 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d269631, d332876, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d269631, d332876, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d269632 q = 1) (hb : d332877 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d269632, d332877, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d269632, d332877, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d269633 q = 1) (hb : d332878 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d269633, d332878, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d269633, d332878, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro102939 (p : Pattern) (ha : d269655 p = 1) (hb : d332888 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d269563 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d269572 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d269600 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d269537 q = 1) (hb : d332873 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d269537, d332873, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro102813 q ha hb
    | true =>
      simp only [d269537, d332873, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro102814 q ha hb
  have h4 (q : Pattern) (ha : d269601 q = 1) (hb : d332874 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d269601, d332874, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d269601, d332874, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d269629 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d269630 q = 1) (hb : d332875 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d269630, d332875, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d269630, d332875, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d269631 q = 1) (hb : d332876 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d269631, d332876, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d269631, d332876, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d269632 q = 1) (hb : d332877 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d269632, d332877, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d269632, d332877, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d269639 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d269644 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d269647 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d269547 q = 1) (hb : d332883 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d269547, d332883, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro102816 q ha hb
    | true =>
      simp only [d269547, d332883, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro102817 q ha hb
  have h13 (q : Pattern) (ha : d269648 q = 1) (hb : d332884 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d269648, d332884, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
    | true =>
      simp only [d269648, d332884, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d269651 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d269652 q = 1) (hb : d332885 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d269652, d332885, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d269652, d332885, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d269653 q = 1) (hb : d332886 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d269653, d332886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
    | true =>
      simp only [d269653, d332886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d269654 q = 1) (hb : d332887 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d269654, d332887, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
    | true =>
      simp only [d269654, d332887, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d269655 q = 1) (hb : d332888 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d269655, d332888, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d269655, d332888, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro102940 (p : Pattern) (ha : d269680 p = 1) (hb : d333269 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d269647 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d269547 q = 1) (hb : d332883 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d269547, d332883, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro102816 q ha hb
    | true =>
      simp only [d269547, d332883, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro102817 q ha hb
  have h3 (q : Pattern) (ha : d269648 q = 1) (hb : d332884 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d269648, d332884, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d269648, d332884, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d269651 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d269652 q = 1) (hb : d332885 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d269652, d332885, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d269652, d332885, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d269678 q = 1) (hb : d332886 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d269678, d332886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d269678, d332886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d269679 q = 1) (hb : d332887 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d269679, d332887, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d269679, d332887, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d269680 q = 1) (hb : d333269 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d269680, d333269, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d269680, d333269, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro102941 (p : Pattern) (ha : d269775 p = 1) (hb : d333021 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d269728 q = 1) (hb : d333001 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d269728, d333001, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro102847 q ha hb
    | true =>
      simp only [d269728, d333001, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro102849 q ha hb
  have h2 (q : Pattern) (ha : d269729 q = 1) (hb : d333002 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d269729, d333002, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d269729, d333002, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d269730 q = 1) (hb : d333003 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d269730, d333003, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d269730, d333003, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d269742 q = 1) (hb : d333011 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d269742, d333011, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro102849 q ha hb
    | true =>
      simp only [d269742, d333011, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro102850 q ha hb
  have h5 (q : Pattern) (ha : d269743 q = 1) (hb : d333012 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d269743, d333012, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d269743, d333012, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d269744 q = 1) (hb : d333013 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d269744, d333013, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d269744, d333013, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d269745 q = 1) (hb : d333014 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d269745, d333014, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d269745, d333014, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d269761 q = 1) (hb : d333011 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d269761, d333011, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro102849 q ha hb
    | true =>
      simp only [d269761, d333011, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro102854 q ha hb
  have h9 (q : Pattern) (ha : d269762 q = 1) (hb : d333012 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d269762, d333012, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d269762, d333012, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d269763 q = 1) (hb : d333013 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d269763, d333013, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d269763, d333013, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d269764 q = 1) (hb : d333019 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d269764, d333019, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d269764, d333019, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d269774 q = 1) (hb : d333020 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d269774, d333020, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d269774, d333020, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d269775 q = 1) (hb : d333021 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d269775, d333021, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d269775, d333021, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h13 p ha hb
theorem andIntro102942 (p : Pattern) (ha : d269781 p = 1) (hb : d333035 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d269776 q = 1) (hb : d333022 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d269776, d333022, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro102941 q ha hb
    | true =>
      simp only [d269776, d333022, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d269777 q = 1) (hb : d333023 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d269777, d333023, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d269777, d333023, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d269767 q = 1) (hb : d333030 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d269767, d333030, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro102855 q ha hb
    | true =>
      simp only [d269767, d333030, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d269768 q = 1) (hb : d333031 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d269768, d333031, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d269768, d333031, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d269778 q = 1) (hb : d333032 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d269778, d333032, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d269778, d333032, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d269779 q = 1) (hb : d333033 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d269779, d333033, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d269779, d333033, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d269780 q = 1) (hb : d333034 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d269780, d333034, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d269780, d333034, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d269781 q = 1) (hb : d333035 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d269781, d333035, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d269781, d333035, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro102943 (p : Pattern) (ha : d269789 p = 1) (hb : d332845 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d69322 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d269783 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d5128 q = 1) (hb : d269784 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d5128, d269784, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d5128, d269784, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro99135 q ha hb
  have h3 (q : Pattern) (ha : d269785 q = 1) (hb : d332827 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d269785, d332827, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d269785, d332827, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d269786 q = 1) (hb : d332828 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d269786, d332828, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d269786, d332828, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d53326 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d1564 q = 1) (hb : d101727 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d1564, d101727, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro99135 q ha hb
    | true =>
      simp only [d1564, d101727, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h8 (q : Pattern) (ha : d269459 q = 1) (hb : d332829 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d269459, d332829, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
    | true =>
      simp only [d269459, d332829, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
  have h9 (q : Pattern) (ha : d269460 q = 1) (hb : d332830 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d269460, d332830, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d269460, d332830, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h10 (q : Pattern) (ha : d269787 q = 1) (hb : d332831 q = 1) : d0 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d269787, d332831, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d269787, d332831, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d269788 q = 1) (hb : d332832 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d269788, d332832, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d269788, d332832, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h12 (q : Pattern) (ha : d269789 q = 1) (hb : d332845 q = 1) : d0 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d269789, d332845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d269789, d332845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  exact h12 p ha hb
theorem andIntro102944 (p : Pattern) (ha : d269795 p = 1) (hb : d333010 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d269722 q = 1) (hb : d332990 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d269722, d332990, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d269722, d332990, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro102805 q ha hb
  have h2 (q : Pattern) (ha : d269482 q = 1) (hb : d332834 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d269482, d332834, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro102805 q ha hb
    | true =>
      simp only [d269482, d332834, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d269723 q = 1) (hb : d332991 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d269723, d332991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d269723, d332991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d269483 q = 1) (hb : d332835 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d269483, d332835, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d269483, d332835, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d269724 q = 1) (hb : d332992 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d269724, d332992, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d269724, d332992, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d269725 q = 1) (hb : d332993 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d269725, d332993, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d269725, d332993, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d269759 q = 1) (hb : d332999 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d269759, d332999, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d269759, d332999, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d269736 q = 1) (hb : d333005 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d269736, d333005, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d269736, d333005, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro102808 q ha hb
  have h9 (q : Pattern) (ha : d269505 q = 1) (hb : d332846 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d269505, d332846, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro102808 q ha hb
    | true =>
      simp only [d269505, d332846, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h10 (q : Pattern) (ha : d269737 q = 1) (hb : d333006 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d269737, d333006, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d269737, d333006, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d269790 q = 1) (hb : d332846 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d269790, d332846, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro102943 q ha hb
    | true =>
      simp only [d269790, d332846, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d269791 q = 1) (hb : d332847 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d269791, d332847, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d269791, d332847, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d269792 q = 1) (hb : d333007 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d269792, d333007, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d269792, d333007, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d269793 q = 1) (hb : d333008 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d269793, d333008, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d269793, d333008, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h15 (q : Pattern) (ha : d269794 q = 1) (hb : d333009 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d269794, d333009, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d269794, d333009, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h16 (q : Pattern) (ha : d269795 q = 1) (hb : d333010 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d269795, d333010, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d269795, d333010, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  exact h16 p ha hb
theorem andIntro102945 (p : Pattern) (ha : d269801 p = 1) (hb : d333029 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d269796 q = 1) (hb : d333011 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d269796, d333011, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro102849 q ha hb
    | true =>
      simp only [d269796, d333011, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro102944 q ha hb
  have h2 (q : Pattern) (ha : d269797 q = 1) (hb : d333012 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d269797, d333012, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d269797, d333012, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d269798 q = 1) (hb : d333013 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d269798, d333013, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d269798, d333013, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d269799 q = 1) (hb : d333019 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d269799, d333019, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d269799, d333019, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d269800 q = 1) (hb : d333028 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d269800, d333028, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d269800, d333028, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d269801 q = 1) (hb : d333029 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d269801, d333029, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d269801, d333029, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro102946 (p : Pattern) (ha : d269807 p = 1) (hb : d333061 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d269802 q = 1) (hb : d333030 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d269802, d333030, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro102945 q ha hb
    | true =>
      simp only [d269802, d333030, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d269803 q = 1) (hb : d333031 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d269803, d333031, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d269803, d333031, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d269804 q = 1) (hb : d333058 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d269804, d333058, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d269804, d333058, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d269805 q = 1) (hb : d333059 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d269805, d333059, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d269805, d333059, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d269806 q = 1) (hb : d333060 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d269806, d333060, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d269806, d333060, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d269807 q = 1) (hb : d333061 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d269807, d333061, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d269807, d333061, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro102947 (p : Pattern) (ha : d269839 p = 1) (hb : d333280 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d269773 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d269808 q = 1) (hb : d333275 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d269808, d333275, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro102942 q ha hb
    | true =>
      simp only [d269808, d333275, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro102946 q ha hb
  have h3 (q : Pattern) (ha : d269809 q = 1) (hb : d333276 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d269809, d333276, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d269809, d333276, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d269835 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d269836 q = 1) (hb : d333277 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d269836, d333277, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d269836, d333277, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d269837 q = 1) (hb : d333278 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d269837, d333278, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d269837, d333278, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d269838 q = 1) (hb : d333279 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d269838, d333279, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d269838, d333279, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d269839 q = 1) (hb : d333280 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d269839, d333280, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d269839, d333280, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro102948 (p : Pattern) (ha : d269856 p = 1) (hb : d333286 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d269555 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d269656 q = 1) (hb : d332889 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d269656, d332889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro102938 q ha hb
    | true =>
      simp only [d269656, d332889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro102939 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d269674 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d269675 q = 1) (hb : d332890 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d269675, d332890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d269675, d332890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d269676 q = 1) (hb : d333267 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d269676, d333267, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d269676, d333267, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d269677 q = 1) (hb : d333268 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d269677, d333268, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d269677, d333268, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d269681 q = 1) (hb : d333270 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d269681, d333270, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d269681, d333270, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro102940 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d269683 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d269684 q = 1) (hb : d333271 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d269684, d333271, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d269684, d333271, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d269685 q = 1) (hb : d333272 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d269685, d333272, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d269685, d333272, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h11 (q : Pattern) (ha : d269686 q = 1) (hb : d333273 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d269686, d333273, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d269686, d333273, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h12 (q : Pattern) (ha : d269687 q = 1) (hb : d333274 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d269687, d333274, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d269687, d333274, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d269840 q = 1) (hb : d333281 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d269840, d333281, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d269840, d333281, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro102947 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d269851 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d269852 q = 1) (hb : d333282 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d269852, d333282, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d269852, d333282, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d269853 q = 1) (hb : d333283 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d269853, d333283, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d269853, d333283, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h17 (q : Pattern) (ha : d269854 q = 1) (hb : d333284 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d269854, d333284, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d269854, d333284, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h18 (q : Pattern) (ha : d269855 q = 1) (hb : d333285 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d269855, d333285, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d269855, d333285, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h19 (q : Pattern) (ha : d269856 q = 1) (hb : d333286 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d269856, d333286, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d269856, d333286, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro102949 (p : Pattern) (ha : d269862 p = 1) (hb : d333292 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d269857 q = 1) (hb : d333287 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d269857, d333287, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d269857, d333287, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro102948 q ha hb
  have h2 (q : Pattern) (ha : d269858 q = 1) (hb : d333288 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d269858, d333288, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d269858, d333288, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d269859 q = 1) (hb : d333289 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d269859, d333289, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d269859, d333289, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d269860 q = 1) (hb : d333290 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d269860, d333290, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d269860, d333290, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d269861 q = 1) (hb : d333291 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d269861, d333291, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d269861, d333291, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d269862 q = 1) (hb : d333292 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d269862, d333292, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d269862, d333292, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro102950 (p : Pattern) (ha : d269868 p = 1) (hb : d333298 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d268313 q = 1) (hb : d333179 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d268313, d333179, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro102911 q ha hb
    | true =>
      simp only [d268313, d333179, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro102917 q ha hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d268585 q = 1) (hb : d333206 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d268585, d333206, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d268585, d333206, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro102923 q ha hb
  have h3 (q : Pattern) (ha : d268586 q = 1) (hb : d333207 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d268586, d333207, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d268586, d333207, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d268956 q = 1) (hb : d333234 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d268956, d333234, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d268956, d333234, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro102929 q ha hb
  have h5 (q : Pattern) (ha : d268957 q = 1) (hb : d333235 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d268957, d333235, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d268957, d333235, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d268958 q = 1) (hb : d333236 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d268958, d333236, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d268958, d333236, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d269422 q = 1) (hb : d333263 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d269422, d333263, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d269422, d333263, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro102937 q ha hb
  have h8 (q : Pattern) (ha : d269423 q = 1) (hb : d333264 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d269423, d333264, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d269423, d333264, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d269424 q = 1) (hb : d333265 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d269424, d333265, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d269424, d333265, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d269425 q = 1) (hb : d333266 q = 1) : d0 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d269425, d333266, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d269425, d333266, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d269863 q = 1) (hb : d333293 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d269863, d333293, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d269863, d333293, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro102949 q ha hb
  have h12 (q : Pattern) (ha : d269864 q = 1) (hb : d333294 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d269864, d333294, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d269864, d333294, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d269865 q = 1) (hb : d333295 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d269865, d333295, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d269865, d333295, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d269866 q = 1) (hb : d333296 q = 1) : d0 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d269866, d333296, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d269866, d333296, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d269867 q = 1) (hb : d333297 q = 1) : d0 q = 1 := by
    cases bit : q 10250 with
    | false =>
      simp only [d269867, d333297, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d269867, d333297, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d269868 q = 1) (hb : d333298 q = 1) : d0 q = 1 := by
    cases bit : q 260 with
    | false =>
      simp only [d269868, d333298, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d269868, d333298, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  exact h16 p ha hb
theorem andIntro102951 (p : Pattern) (ha : d269874 p = 1) (hb : d333304 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d269869 q = 1) (hb : d333299 q = 1) : d0 q = 1 := by
    cases bit : q 259 with
    | false =>
      simp only [d269869, d333299, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro102950 q ha hb
    | true =>
      simp only [d269869, d333299, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d269870 q = 1) (hb : d333300 q = 1) : d0 q = 1 := by
    cases bit : q 258 with
    | false =>
      simp only [d269870, d333300, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d269870, d333300, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d269871 q = 1) (hb : d333301 q = 1) : d0 q = 1 := by
    cases bit : q 257 with
    | false =>
      simp only [d269871, d333301, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d269871, d333301, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d269872 q = 1) (hb : d333302 q = 1) : d0 q = 1 := by
    cases bit : q 256 with
    | false =>
      simp only [d269872, d333302, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d269872, d333302, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d269873 q = 1) (hb : d333303 q = 1) : d0 q = 1 := by
    cases bit : q 255 with
    | false =>
      simp only [d269873, d333303, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d269873, d333303, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d269874 q = 1) (hb : d333304 q = 1) : d0 q = 1 := by
    cases bit : q 254 with
    | false =>
      simp only [d269874, d333304, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d269874, d333304, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro102952 (p : Pattern) (ha : d269880 p = 1) (hb : d333310 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d269875 q = 1) (hb : d333305 q = 1) : d0 q = 1 := by
    cases bit : q 253 with
    | false =>
      simp only [d269875, d333305, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro102951 q ha hb
    | true =>
      simp only [d269875, d333305, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d269876 q = 1) (hb : d333306 q = 1) : d0 q = 1 := by
    cases bit : q 252 with
    | false =>
      simp only [d269876, d333306, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d269876, d333306, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d269877 q = 1) (hb : d333307 q = 1) : d0 q = 1 := by
    cases bit : q 251 with
    | false =>
      simp only [d269877, d333307, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d269877, d333307, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d269878 q = 1) (hb : d333308 q = 1) : d0 q = 1 := by
    cases bit : q 250 with
    | false =>
      simp only [d269878, d333308, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d269878, d333308, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d269879 q = 1) (hb : d333309 q = 1) : d0 q = 1 := by
    cases bit : q 249 with
    | false =>
      simp only [d269879, d333309, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d269879, d333309, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d269880 q = 1) (hb : d333310 q = 1) : d0 q = 1 := by
    cases bit : q 245 with
    | false =>
      simp only [d269880, d333310, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d269880, d333310, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro102953 (p : Pattern) (ha : d269886 p = 1) (hb : d333316 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d269881 q = 1) (hb : d333311 q = 1) : d0 q = 1 := by
    cases bit : q 200 with
    | false =>
      simp only [d269881, d333311, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro102952 q ha hb
    | true =>
      simp only [d269881, d333311, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d269882 q = 1) (hb : d333312 q = 1) : d0 q = 1 := by
    cases bit : q 199 with
    | false =>
      simp only [d269882, d333312, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d269882, d333312, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d269883 q = 1) (hb : d333313 q = 1) : d0 q = 1 := by
    cases bit : q 186 with
    | false =>
      simp only [d269883, d333313, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d269883, d333313, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d269884 q = 1) (hb : d333314 q = 1) : d0 q = 1 := by
    cases bit : q 185 with
    | false =>
      simp only [d269884, d333314, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d269884, d333314, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d269885 q = 1) (hb : d333315 q = 1) : d0 q = 1 := by
    cases bit : q 184 with
    | false =>
      simp only [d269885, d333315, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d269885, d333315, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d269886 q = 1) (hb : d333316 q = 1) : d0 q = 1 := by
    cases bit : q 181 with
    | false =>
      simp only [d269886, d333316, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d269886, d333316, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro102954 (p : Pattern) (ha : d269892 p = 1) (hb : d333322 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d269887 q = 1) (hb : d333317 q = 1) : d0 q = 1 := by
    cases bit : q 177 with
    | false =>
      simp only [d269887, d333317, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro102953 q ha hb
    | true =>
      simp only [d269887, d333317, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d269888 q = 1) (hb : d333318 q = 1) : d0 q = 1 := by
    cases bit : q 164 with
    | false =>
      simp only [d269888, d333318, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d269888, d333318, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d269889 q = 1) (hb : d333319 q = 1) : d0 q = 1 := by
    cases bit : q 156 with
    | false =>
      simp only [d269889, d333319, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d269889, d333319, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d269890 q = 1) (hb : d333320 q = 1) : d0 q = 1 := by
    cases bit : q 155 with
    | false =>
      simp only [d269890, d333320, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d269890, d333320, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d269891 q = 1) (hb : d333321 q = 1) : d0 q = 1 := by
    cases bit : q 134 with
    | false =>
      simp only [d269891, d333321, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d269891, d333321, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d269892 q = 1) (hb : d333322 q = 1) : d0 q = 1 := by
    cases bit : q 133 with
    | false =>
      simp only [d269892, d333322, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d269892, d333322, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro102955 (p : Pattern) (ha : d269898 p = 1) (hb : d333328 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d269893 q = 1) (hb : d333323 q = 1) : d0 q = 1 := by
    cases bit : q 120 with
    | false =>
      simp only [d269893, d333323, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro102954 q ha hb
    | true =>
      simp only [d269893, d333323, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d269894 q = 1) (hb : d333324 q = 1) : d0 q = 1 := by
    cases bit : q 118 with
    | false =>
      simp only [d269894, d333324, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d269894, d333324, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d269895 q = 1) (hb : d333325 q = 1) : d0 q = 1 := by
    cases bit : q 114 with
    | false =>
      simp only [d269895, d333325, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d269895, d333325, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d269896 q = 1) (hb : d333326 q = 1) : d0 q = 1 := by
    cases bit : q 111 with
    | false =>
      simp only [d269896, d333326, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d269896, d333326, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d269897 q = 1) (hb : d333327 q = 1) : d0 q = 1 := by
    cases bit : q 98 with
    | false =>
      simp only [d269897, d333327, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d269897, d333327, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d269898 q = 1) (hb : d333328 q = 1) : d0 q = 1 := by
    cases bit : q 97 with
    | false =>
      simp only [d269898, d333328, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d269898, d333328, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro102956 (p : Pattern) (ha : d269904 p = 1) (hb : d333334 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d269899 q = 1) (hb : d333329 q = 1) : d0 q = 1 := by
    cases bit : q 94 with
    | false =>
      simp only [d269899, d333329, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro102955 q ha hb
    | true =>
      simp only [d269899, d333329, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d269900 q = 1) (hb : d333330 q = 1) : d0 q = 1 := by
    cases bit : q 76 with
    | false =>
      simp only [d269900, d333330, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d269900, d333330, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d269901 q = 1) (hb : d333331 q = 1) : d0 q = 1 := by
    cases bit : q 67 with
    | false =>
      simp only [d269901, d333331, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d269901, d333331, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d269902 q = 1) (hb : d333332 q = 1) : d0 q = 1 := by
    cases bit : q 52 with
    | false =>
      simp only [d269902, d333332, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d269902, d333332, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d269903 q = 1) (hb : d333333 q = 1) : d0 q = 1 := by
    cases bit : q 47 with
    | false =>
      simp only [d269903, d333333, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d269903, d333333, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d269904 q = 1) (hb : d333334 q = 1) : d0 q = 1 := by
    cases bit : q 46 with
    | false =>
      simp only [d269904, d333334, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d269904, d333334, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro102957 (p : Pattern) (ha : d269910 p = 1) (hb : d333340 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d269905 q = 1) (hb : d333335 q = 1) : d0 q = 1 := by
    cases bit : q 45 with
    | false =>
      simp only [d269905, d333335, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro102956 q ha hb
    | true =>
      simp only [d269905, d333335, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d269906 q = 1) (hb : d333336 q = 1) : d0 q = 1 := by
    cases bit : q 30 with
    | false =>
      simp only [d269906, d333336, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d269906, d333336, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d269907 q = 1) (hb : d333337 q = 1) : d0 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d269907, d333337, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d269907, d333337, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d269908 q = 1) (hb : d333338 q = 1) : d0 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d269908, d333338, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d269908, d333338, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d269909 q = 1) (hb : d333339 q = 1) : d0 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d269909, d333339, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d269909, d333339, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d269910 q = 1) (hb : d333340 q = 1) : d0 q = 1 := by
    cases bit : q 25 with
    | false =>
      simp only [d269910, d333340, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d269910, d333340, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro102958 (p : Pattern) (ha : d269953 p = 1) (hb : d331425 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d36106 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d36112 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d36145 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d331361 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d269949 q = 1) (hb : d331421 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d269949, d331421, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d269949, d331421, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d36174 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d269950 q = 1) (hb : d331422 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d269950, d331422, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d269950, d331422, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d269951 q = 1) (hb : d331423 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d269951, d331423, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d269951, d331423, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d269952 q = 1) (hb : d331424 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d269952, d331424, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d269952, d331424, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d269953 q = 1) (hb : d331425 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d269953, d331425, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d269953, d331425, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro102959 (p : Pattern) (ha : d269958 p = 1) (hb : d331432 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d36106 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d36112 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d36145 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d331361 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d269949 q = 1) (hb : d331421 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d269949, d331421, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d269949, d331421, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d36174 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d269950 q = 1) (hb : d331422 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d269950, d331422, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d269950, d331422, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d269951 q = 1) (hb : d331423 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d269951, d331423, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d269951, d331423, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d269952 q = 1) (hb : d331424 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d269952, d331424, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d269952, d331424, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d36183 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d36187 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d36189 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d331368 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d269954 q = 1) (hb : d331428 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d269954, d331428, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
    | true =>
      simp only [d269954, d331428, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d36195 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d269955 q = 1) (hb : d331429 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d269955, d331429, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d269955, d331429, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d269956 q = 1) (hb : d331430 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d269956, d331430, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
    | true =>
      simp only [d269956, d331430, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d269957 q = 1) (hb : d331431 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d269957, d331431, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
    | true =>
      simp only [d269957, d331431, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d269958 q = 1) (hb : d331432 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d269958, d331432, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d269958, d331432, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro102960 (p : Pattern) (ha : d269965 p = 1) (hb : d333130 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d36189 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d331368 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d269954 q = 1) (hb : d331428 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d269954, d331428, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d269954, d331428, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d36195 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d269955 q = 1) (hb : d331429 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d269955, d331429, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d269955, d331429, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d269963 q = 1) (hb : d331430 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d269963, d331430, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d269963, d331430, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d269964 q = 1) (hb : d331431 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d269964, d331431, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d269964, d331431, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d269965 q = 1) (hb : d333130 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d269965, d333130, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d269965, d333130, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro102961 (p : Pattern) (ha : d269975 p = 1) (hb : d333140 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d36237 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d331404 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d269971 q = 1) (hb : d333136 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d269971, d333136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d269971, d333136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d36263 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d269972 q = 1) (hb : d333137 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d269972, d333137, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d269972, d333137, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d269973 q = 1) (hb : d333138 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d269973, d333138, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d269973, d333138, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d269974 q = 1) (hb : d333139 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d269974, d333139, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d269974, d333139, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d269975 q = 1) (hb : d333140 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d269975, d333140, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d269975, d333140, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro102962 (p : Pattern) (ha : d269981 p = 1) (hb : d333146 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d36100 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d269959 q = 1) (hb : d331433 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d269959, d331433, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro102958 q ha hb
    | true =>
      simp only [d269959, d331433, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro102959 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d36202 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d269960 q = 1) (hb : d331434 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d269960, d331434, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d269960, d331434, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d269961 q = 1) (hb : d333128 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d269961, d333128, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d269961, d333128, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d269962 q = 1) (hb : d333129 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d269962, d333129, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d269962, d333129, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d269966 q = 1) (hb : d333131 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d269966, d333131, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d269966, d333131, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro102960 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d407 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d269967 q = 1) (hb : d333132 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d269967, d333132, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d269967, d333132, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d269968 q = 1) (hb : d333133 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d269968, d333133, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d269968, d333133, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h11 (q : Pattern) (ha : d269969 q = 1) (hb : d333134 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d269969, d333134, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d269969, d333134, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h12 (q : Pattern) (ha : d269970 q = 1) (hb : d333135 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d269970, d333135, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d269970, d333135, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d269976 q = 1) (hb : d333141 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d269976, d333141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d269976, d333141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro102961 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d463 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d269977 q = 1) (hb : d333142 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d269977, d333142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d269977, d333142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d269978 q = 1) (hb : d333143 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d269978, d333143, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d269978, d333143, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h17 (q : Pattern) (ha : d269979 q = 1) (hb : d333144 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d269979, d333144, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d269979, d333144, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h18 (q : Pattern) (ha : d269980 q = 1) (hb : d333145 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d269980, d333145, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d269980, d333145, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h19 (q : Pattern) (ha : d269981 q = 1) (hb : d333146 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d269981, d333146, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d269981, d333146, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro102963 (p : Pattern) (ha : d269987 p = 1) (hb : d333152 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d99 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d53648 q = 1) (hb : d269944 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d53648, d269944, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d53648, d269944, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro68689 q ha hb
  have h3 (q : Pattern) (ha : d53649 q = 1) (hb : d269945 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d53649, d269945, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d53649, d269945, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d53650 q = 1) (hb : d269946 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d53650, d269946, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d53650, d269946, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d53651 q = 1) (hb : d269947 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d53651, d269947, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d53651, d269947, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d53652 q = 1) (hb : d269948 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d53652, d269948, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53652, d269948, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d269982 q = 1) (hb : d333147 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d269982, d333147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d269982, d333147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro102962 q ha hb
  have h8 (q : Pattern) (ha : d269983 q = 1) (hb : d333148 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d269983, d333148, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d269983, d333148, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d269984 q = 1) (hb : d333149 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d269984, d333149, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d269984, d333149, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d269985 q = 1) (hb : d333150 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d269985, d333150, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d269985, d333150, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d269986 q = 1) (hb : d333151 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d269986, d333151, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d269986, d333151, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d269987 q = 1) (hb : d333152 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d269987, d333152, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
    | true =>
      simp only [d269987, d333152, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  exact h12 p ha hb
theorem andIntro102964 (p : Pattern) (ha : d269992 p = 1) (hb : d331595 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d36323 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d36332 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d36376 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d331590 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d269988 q = 1) (hb : d331591 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d269988, d331591, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d269988, d331591, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d36425 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d269989 q = 1) (hb : d331592 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d269989, d331592, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d269989, d331592, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d269990 q = 1) (hb : d331593 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d269990, d331593, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d269990, d331593, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d269991 q = 1) (hb : d331594 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d269991, d331594, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d269991, d331594, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d269992 q = 1) (hb : d331595 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d269992, d331595, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d269992, d331595, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro102965 (p : Pattern) (ha : d269997 p = 1) (hb : d331605 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d36323 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d36332 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d36376 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d331590 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d269988 q = 1) (hb : d331591 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d269988, d331591, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d269988, d331591, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d36425 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d269989 q = 1) (hb : d331592 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d269989, d331592, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d269989, d331592, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d269990 q = 1) (hb : d331593 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d269990, d331593, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d269990, d331593, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d269991 q = 1) (hb : d331594 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d269991, d331594, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d269991, d331594, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d36435 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d36440 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d36442 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d331600 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d269993 q = 1) (hb : d331601 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d269993, d331601, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
    | true =>
      simp only [d269993, d331601, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d36449 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d269994 q = 1) (hb : d331602 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d269994, d331602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d269994, d331602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d269995 q = 1) (hb : d331603 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d269995, d331603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
    | true =>
      simp only [d269995, d331603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d269996 q = 1) (hb : d331604 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d269996, d331604, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
    | true =>
      simp only [d269996, d331604, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d269997 q = 1) (hb : d331605 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d269997, d331605, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d269997, d331605, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro102966 (p : Pattern) (ha : d270004 p = 1) (hb : d333155 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d36442 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d331600 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d269993 q = 1) (hb : d331601 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d269993, d331601, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d269993, d331601, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d36449 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d269994 q = 1) (hb : d331602 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d269994, d331602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d269994, d331602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d270002 q = 1) (hb : d331603 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d270002, d331603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d270002, d331603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d270003 q = 1) (hb : d331604 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d270003, d331604, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d270003, d331604, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d270004 q = 1) (hb : d333155 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d270004, d333155, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d270004, d333155, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro102967 (p : Pattern) (ha : d270014 p = 1) (hb : d333166 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d36525 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d333161 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d270010 q = 1) (hb : d333162 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d270010, d333162, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d270010, d333162, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d36565 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d270011 q = 1) (hb : d333163 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d270011, d333163, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d270011, d333163, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d270012 q = 1) (hb : d333164 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d270012, d333164, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d270012, d333164, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d270013 q = 1) (hb : d333165 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d270013, d333165, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d270013, d333165, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d270014 q = 1) (hb : d333166 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d270014, d333166, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d270014, d333166, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro102968 (p : Pattern) (ha : d270020 p = 1) (hb : d333172 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d36315 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d269998 q = 1) (hb : d331606 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d269998, d331606, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro102964 q ha hb
    | true =>
      simp only [d269998, d331606, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro102965 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d36467 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d269999 q = 1) (hb : d331607 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d269999, d331607, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d269999, d331607, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d270000 q = 1) (hb : d333153 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d270000, d333153, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d270000, d333153, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d270001 q = 1) (hb : d333154 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d270001, d333154, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d270001, d333154, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d270005 q = 1) (hb : d333156 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d270005, d333156, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d270005, d333156, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro102966 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d36476 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d270006 q = 1) (hb : d333157 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d270006, d333157, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d270006, d333157, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d270007 q = 1) (hb : d333158 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d270007, d333158, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d270007, d333158, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h11 (q : Pattern) (ha : d270008 q = 1) (hb : d333159 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d270008, d333159, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d270008, d333159, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h12 (q : Pattern) (ha : d270009 q = 1) (hb : d333160 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d270009, d333160, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d270009, d333160, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d270015 q = 1) (hb : d333167 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d270015, d333167, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d270015, d333167, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro102967 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d36581 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d270016 q = 1) (hb : d333168 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d270016, d333168, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d270016, d333168, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d270017 q = 1) (hb : d333169 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d270017, d333169, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d270017, d333169, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h17 (q : Pattern) (ha : d270018 q = 1) (hb : d333170 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d270018, d333170, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d270018, d333170, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h18 (q : Pattern) (ha : d270019 q = 1) (hb : d333171 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d270019, d333171, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d270019, d333171, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h19 (q : Pattern) (ha : d270020 q = 1) (hb : d333172 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d270020, d333172, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d270020, d333172, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro102969 (p : Pattern) (ha : d270026 p = 1) (hb : d333178 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d270021 q = 1) (hb : d333173 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d270021, d333173, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d270021, d333173, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro102968 q ha hb
  have h2 (q : Pattern) (ha : d270022 q = 1) (hb : d333174 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d270022, d333174, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d270022, d333174, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d270023 q = 1) (hb : d333175 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d270023, d333175, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d270023, d333175, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d270024 q = 1) (hb : d333176 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d270024, d333176, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d270024, d333176, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d270025 q = 1) (hb : d333177 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d270025, d333177, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d270025, d333177, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d270026 q = 1) (hb : d333178 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d270026, d333178, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d270026, d333178, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro102970 (p : Pattern) (ha : d270032 p = 1) (hb : d331845 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d36655 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d36664 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d36708 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d331840 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d270028 q = 1) (hb : d331841 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d270028, d331841, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d270028, d331841, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d36776 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d270029 q = 1) (hb : d331842 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d270029, d331842, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d270029, d331842, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d270030 q = 1) (hb : d331843 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d270030, d331843, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d270030, d331843, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d270031 q = 1) (hb : d331844 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d270031, d331844, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d270031, d331844, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d270032 q = 1) (hb : d331845 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d270032, d331845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d270032, d331845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro102971 (p : Pattern) (ha : d270037 p = 1) (hb : d331855 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d36655 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d36664 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d36708 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d331840 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d270028 q = 1) (hb : d331841 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d270028, d331841, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d270028, d331841, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d36776 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d270029 q = 1) (hb : d331842 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d270029, d331842, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d270029, d331842, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d270030 q = 1) (hb : d331843 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d270030, d331843, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d270030, d331843, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d270031 q = 1) (hb : d331844 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d270031, d331844, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d270031, d331844, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d36786 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d36791 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d36793 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d331850 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d270033 q = 1) (hb : d331851 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d270033, d331851, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
    | true =>
      simp only [d270033, d331851, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d36800 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d270034 q = 1) (hb : d331852 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d270034, d331852, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d270034, d331852, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d270035 q = 1) (hb : d331853 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d270035, d331853, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
    | true =>
      simp only [d270035, d331853, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d270036 q = 1) (hb : d331854 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d270036, d331854, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
    | true =>
      simp only [d270036, d331854, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d270037 q = 1) (hb : d331855 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d270037, d331855, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d270037, d331855, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro102972 (p : Pattern) (ha : d270044 p = 1) (hb : d333182 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d36793 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d331850 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d270033 q = 1) (hb : d331851 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d270033, d331851, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d270033, d331851, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d36800 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d270034 q = 1) (hb : d331852 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d270034, d331852, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d270034, d331852, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d270042 q = 1) (hb : d331853 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d270042, d331853, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d270042, d331853, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d270043 q = 1) (hb : d331854 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d270043, d331854, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d270043, d331854, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d270044 q = 1) (hb : d333182 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d270044, d333182, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d270044, d333182, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro102973 (p : Pattern) (ha : d270054 p = 1) (hb : d333193 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d36893 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d333188 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d270050 q = 1) (hb : d333189 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d270050, d333189, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d270050, d333189, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d36948 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d270051 q = 1) (hb : d333190 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d270051, d333190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d270051, d333190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d270052 q = 1) (hb : d333191 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d270052, d333191, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d270052, d333191, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d270053 q = 1) (hb : d333192 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d270053, d333192, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d270053, d333192, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d270054 q = 1) (hb : d333193 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d270054, d333193, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d270054, d333193, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro102974 (p : Pattern) (ha : d270060 p = 1) (hb : d333199 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d36647 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d270038 q = 1) (hb : d331856 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d270038, d331856, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro102970 q ha hb
    | true =>
      simp only [d270038, d331856, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro102971 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d36818 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d270039 q = 1) (hb : d331857 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d270039, d331857, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d270039, d331857, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d270040 q = 1) (hb : d333180 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d270040, d333180, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d270040, d333180, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d270041 q = 1) (hb : d333181 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d270041, d333181, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d270041, d333181, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d270045 q = 1) (hb : d333183 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d270045, d333183, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d270045, d333183, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro102972 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d36827 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d270046 q = 1) (hb : d333184 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d270046, d333184, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d270046, d333184, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d270047 q = 1) (hb : d333185 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d270047, d333185, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d270047, d333185, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h11 (q : Pattern) (ha : d270048 q = 1) (hb : d333186 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d270048, d333186, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d270048, d333186, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h12 (q : Pattern) (ha : d270049 q = 1) (hb : d333187 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d270049, d333187, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d270049, d333187, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d270055 q = 1) (hb : d333194 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d270055, d333194, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d270055, d333194, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro102973 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d36964 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d270056 q = 1) (hb : d333195 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d270056, d333195, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d270056, d333195, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d270057 q = 1) (hb : d333196 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d270057, d333196, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d270057, d333196, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h17 (q : Pattern) (ha : d270058 q = 1) (hb : d333197 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d270058, d333197, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d270058, d333197, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h18 (q : Pattern) (ha : d270059 q = 1) (hb : d333198 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d270059, d333198, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d270059, d333198, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h19 (q : Pattern) (ha : d270060 q = 1) (hb : d333199 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d270060, d333199, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d270060, d333199, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro102975 (p : Pattern) (ha : d270066 p = 1) (hb : d333205 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d270061 q = 1) (hb : d333200 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d270061, d333200, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d270061, d333200, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro102974 q ha hb
  have h2 (q : Pattern) (ha : d270062 q = 1) (hb : d333201 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d270062, d333201, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d270062, d333201, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d270063 q = 1) (hb : d333202 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d270063, d333202, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d270063, d333202, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d270064 q = 1) (hb : d333203 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d270064, d333203, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d270064, d333203, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d270065 q = 1) (hb : d333204 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d270065, d333204, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d270065, d333204, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d270066 q = 1) (hb : d333205 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d270066, d333205, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d270066, d333205, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro102976 (p : Pattern) (ha : d270073 p = 1) (hb : d332173 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d37086 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d37095 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d37145 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d332168 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d270069 q = 1) (hb : d332169 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d270069, d332169, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d270069, d332169, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d37247 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d270070 q = 1) (hb : d332170 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d270070, d332170, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d270070, d332170, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d270071 q = 1) (hb : d332171 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d270071, d332171, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d270071, d332171, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d270072 q = 1) (hb : d332172 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d270072, d332172, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d270072, d332172, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d270073 q = 1) (hb : d332173 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d270073, d332173, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d270073, d332173, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro102977 (p : Pattern) (ha : d270078 p = 1) (hb : d332183 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d37086 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d37095 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d37145 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d332168 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d270069 q = 1) (hb : d332169 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d270069, d332169, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d270069, d332169, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d37247 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d270070 q = 1) (hb : d332170 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d270070, d332170, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d270070, d332170, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d270071 q = 1) (hb : d332171 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d270071, d332171, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d270071, d332171, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d270072 q = 1) (hb : d332172 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d270072, d332172, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d270072, d332172, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d37257 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d37262 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d37264 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d332178 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d270074 q = 1) (hb : d332179 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d270074, d332179, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
    | true =>
      simp only [d270074, d332179, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d37271 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d270075 q = 1) (hb : d332180 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d270075, d332180, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d270075, d332180, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d270076 q = 1) (hb : d332181 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d270076, d332181, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
    | true =>
      simp only [d270076, d332181, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d270077 q = 1) (hb : d332182 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d270077, d332182, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
    | true =>
      simp only [d270077, d332182, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d270078 q = 1) (hb : d332183 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d270078, d332183, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d270078, d332183, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro102978 (p : Pattern) (ha : d270085 p = 1) (hb : d333210 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d37264 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d332178 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d270074 q = 1) (hb : d332179 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d270074, d332179, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d270074, d332179, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d37271 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d270075 q = 1) (hb : d332180 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d270075, d332180, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d270075, d332180, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d270083 q = 1) (hb : d332181 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d270083, d332181, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d270083, d332181, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d270084 q = 1) (hb : d332182 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d270084, d332182, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d270084, d332182, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d270085 q = 1) (hb : d333210 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d270085, d333210, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d270085, d333210, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro102979 (p : Pattern) (ha : d270095 p = 1) (hb : d333221 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d37391 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d333216 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d270091 q = 1) (hb : d333217 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d270091, d333217, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d270091, d333217, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d37464 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d270092 q = 1) (hb : d333218 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d270092, d333218, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d270092, d333218, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d270093 q = 1) (hb : d333219 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d270093, d333219, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d270093, d333219, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d270094 q = 1) (hb : d333220 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d270094, d333220, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d270094, d333220, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d270095 q = 1) (hb : d333221 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d270095, d333221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d270095, d333221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro102980 (p : Pattern) (ha : d270101 p = 1) (hb : d333227 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d37078 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d270079 q = 1) (hb : d332184 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d270079, d332184, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro102976 q ha hb
    | true =>
      simp only [d270079, d332184, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro102977 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d37289 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d270080 q = 1) (hb : d332185 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d270080, d332185, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d270080, d332185, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d270081 q = 1) (hb : d333208 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d270081, d333208, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d270081, d333208, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d270082 q = 1) (hb : d333209 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d270082, d333209, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d270082, d333209, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d270086 q = 1) (hb : d333211 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d270086, d333211, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d270086, d333211, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro102978 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d37298 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d270087 q = 1) (hb : d333212 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d270087, d333212, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d270087, d333212, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d270088 q = 1) (hb : d333213 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d270088, d333213, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d270088, d333213, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h11 (q : Pattern) (ha : d270089 q = 1) (hb : d333214 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d270089, d333214, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d270089, d333214, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h12 (q : Pattern) (ha : d270090 q = 1) (hb : d333215 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d270090, d333215, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d270090, d333215, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d270096 q = 1) (hb : d333222 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d270096, d333222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d270096, d333222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro102979 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d37480 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d270097 q = 1) (hb : d333223 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d270097, d333223, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d270097, d333223, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d270098 q = 1) (hb : d333224 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d270098, d333224, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d270098, d333224, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h17 (q : Pattern) (ha : d270099 q = 1) (hb : d333225 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d270099, d333225, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d270099, d333225, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h18 (q : Pattern) (ha : d270100 q = 1) (hb : d333226 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d270100, d333226, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d270100, d333226, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h19 (q : Pattern) (ha : d270101 q = 1) (hb : d333227 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d270101, d333227, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d270101, d333227, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro102981 (p : Pattern) (ha : d270107 p = 1) (hb : d333233 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d270102 q = 1) (hb : d333228 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d270102, d333228, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d270102, d333228, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro102980 q ha hb
  have h2 (q : Pattern) (ha : d270103 q = 1) (hb : d333229 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d270103, d333229, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d270103, d333229, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d270104 q = 1) (hb : d333230 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d270104, d333230, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d270104, d333230, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d270105 q = 1) (hb : d333231 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d270105, d333231, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d270105, d333231, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d270106 q = 1) (hb : d333232 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d270106, d333232, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d270106, d333232, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d270107 q = 1) (hb : d333233 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d270107, d333233, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d270107, d333233, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro102982 (p : Pattern) (ha : d271084 p = 1) (hb : d332545 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d37648 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d37657 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d37707 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d332540 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d271080 q = 1) (hb : d332541 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d271080, d332541, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d271080, d332541, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d37864 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d271081 q = 1) (hb : d332542 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d271081, d332542, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d271081, d332542, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d271082 q = 1) (hb : d332543 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d271082, d332543, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d271082, d332543, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d271083 q = 1) (hb : d332544 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d271083, d332544, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d271083, d332544, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d271084 q = 1) (hb : d332545 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d271084, d332545, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d271084, d332545, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro102983 (p : Pattern) (ha : d271089 p = 1) (hb : d332555 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d37648 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d37657 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d37707 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d332540 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d271080 q = 1) (hb : d332541 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d271080, d332541, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d271080, d332541, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d37864 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d271081 q = 1) (hb : d332542 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d271081, d332542, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d271081, d332542, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d271082 q = 1) (hb : d332543 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d271082, d332543, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d271082, d332543, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d271083 q = 1) (hb : d332544 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d271083, d332544, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d271083, d332544, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d37874 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d37879 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d37882 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d332550 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d271085 q = 1) (hb : d332551 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d271085, d332551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
    | true =>
      simp only [d271085, d332551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d37889 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d271086 q = 1) (hb : d332552 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d271086, d332552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d271086, d332552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d271087 q = 1) (hb : d332553 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d271087, d332553, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
    | true =>
      simp only [d271087, d332553, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d271088 q = 1) (hb : d332554 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d271088, d332554, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
    | true =>
      simp only [d271088, d332554, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d271089 q = 1) (hb : d332555 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d271089, d332555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d271089, d332555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro102984 (p : Pattern) (ha : d271096 p = 1) (hb : d333239 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d37882 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d332550 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d271085 q = 1) (hb : d332551 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d271085, d332551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d271085, d332551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d37889 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d271086 q = 1) (hb : d332552 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d271086, d332552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d271086, d332552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d271094 q = 1) (hb : d332553 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d271094, d332553, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d271094, d332553, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d271095 q = 1) (hb : d332554 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d271095, d332554, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d271095, d332554, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d271096 q = 1) (hb : d333239 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d271096, d333239, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d271096, d333239, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro102985 (p : Pattern) (ha : d271106 p = 1) (hb : d333250 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d38025 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d333245 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d271102 q = 1) (hb : d333246 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d271102, d333246, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d271102, d333246, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d38123 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d271103 q = 1) (hb : d333247 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d271103, d333247, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d271103, d333247, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d271104 q = 1) (hb : d333248 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d271104, d333248, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d271104, d333248, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d271105 q = 1) (hb : d333249 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d271105, d333249, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d271105, d333249, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d271106 q = 1) (hb : d333250 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d271106, d333250, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d271106, d333250, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro102986 (p : Pattern) (ha : d271112 p = 1) (hb : d333256 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d37640 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d271090 q = 1) (hb : d332556 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d271090, d332556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro102982 q ha hb
    | true =>
      simp only [d271090, d332556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro102983 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d37912 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d271091 q = 1) (hb : d332557 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d271091, d332557, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d271091, d332557, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d271092 q = 1) (hb : d333237 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d271092, d333237, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d271092, d333237, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d271093 q = 1) (hb : d333238 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d271093, d333238, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d271093, d333238, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d271097 q = 1) (hb : d333240 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d271097, d333240, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d271097, d333240, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro102984 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d37921 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d271098 q = 1) (hb : d333241 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d271098, d333241, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d271098, d333241, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d271099 q = 1) (hb : d333242 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d271099, d333242, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d271099, d333242, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h11 (q : Pattern) (ha : d271100 q = 1) (hb : d333243 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d271100, d333243, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d271100, d333243, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h12 (q : Pattern) (ha : d271101 q = 1) (hb : d333244 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d271101, d333244, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d271101, d333244, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d271107 q = 1) (hb : d333251 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d271107, d333251, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d271107, d333251, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro102985 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d38139 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d271108 q = 1) (hb : d333252 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d271108, d333252, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d271108, d333252, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d271109 q = 1) (hb : d333253 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d271109, d333253, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d271109, d333253, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h17 (q : Pattern) (ha : d271110 q = 1) (hb : d333254 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d271110, d333254, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d271110, d333254, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h18 (q : Pattern) (ha : d271111 q = 1) (hb : d333255 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d271111, d333255, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d271111, d333255, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h19 (q : Pattern) (ha : d271112 q = 1) (hb : d333256 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d271112, d333256, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d271112, d333256, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro102987 (p : Pattern) (ha : d271118 p = 1) (hb : d333262 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d271113 q = 1) (hb : d333257 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d271113, d333257, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d271113, d333257, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro102986 q ha hb
  have h2 (q : Pattern) (ha : d271114 q = 1) (hb : d333258 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d271114, d333258, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d271114, d333258, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d271115 q = 1) (hb : d333259 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d271115, d333259, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d271115, d333259, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d271116 q = 1) (hb : d333260 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d271116, d333260, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d271116, d333260, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d271117 q = 1) (hb : d333261 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d271117, d333261, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d271117, d333261, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d271118 q = 1) (hb : d333262 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d271118, d333262, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d271118, d333262, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro102988 (p : Pattern) (ha : d271127 p = 1) (hb : d332878 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d38292 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d38301 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d38329 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d332873 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d271123 q = 1) (hb : d332874 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d271123, d332874, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d271123, d332874, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d38470 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d271124 q = 1) (hb : d332875 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d271124, d332875, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d271124, d332875, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d271125 q = 1) (hb : d332876 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d271125, d332876, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d271125, d332876, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d271126 q = 1) (hb : d332877 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d271126, d332877, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d271126, d332877, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d271127 q = 1) (hb : d332878 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d271127, d332878, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d271127, d332878, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro102989 (p : Pattern) (ha : d271132 p = 1) (hb : d332888 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d38292 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d38301 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d38329 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d332873 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d271123 q = 1) (hb : d332874 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d271123, d332874, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d271123, d332874, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d38470 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d271124 q = 1) (hb : d332875 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d271124, d332875, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d271124, d332875, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d271125 q = 1) (hb : d332876 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d271125, d332876, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d271125, d332876, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d271126 q = 1) (hb : d332877 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d271126, d332877, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d271126, d332877, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d38480 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d38485 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d38488 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d332883 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d271128 q = 1) (hb : d332884 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d271128, d332884, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
    | true =>
      simp only [d271128, d332884, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d38495 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d271129 q = 1) (hb : d332885 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d271129, d332885, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d271129, d332885, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d271130 q = 1) (hb : d332886 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d271130, d332886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
    | true =>
      simp only [d271130, d332886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d271131 q = 1) (hb : d332887 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d271131, d332887, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
    | true =>
      simp only [d271131, d332887, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d271132 q = 1) (hb : d332888 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d271132, d332888, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d271132, d332888, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro102990 (p : Pattern) (ha : d271139 p = 1) (hb : d333269 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d38488 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d332883 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d271128 q = 1) (hb : d332884 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d271128, d332884, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d271128, d332884, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d38495 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d271129 q = 1) (hb : d332885 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d271129, d332885, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d271129, d332885, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d271137 q = 1) (hb : d332886 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d271137, d332886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d271137, d332886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d271138 q = 1) (hb : d332887 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d271138, d332887, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d271138, d332887, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d271139 q = 1) (hb : d333269 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d271139, d333269, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d271139, d333269, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro102991 (p : Pattern) (ha : d271149 p = 1) (hb : d333280 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d38617 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d333275 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d271145 q = 1) (hb : d333276 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d271145, d333276, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d271145, d333276, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d38737 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d271146 q = 1) (hb : d333277 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d271146, d333277, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d271146, d333277, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d271147 q = 1) (hb : d333278 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d271147, d333278, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d271147, d333278, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d271148 q = 1) (hb : d333279 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d271148, d333279, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d271148, d333279, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d271149 q = 1) (hb : d333280 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d271149, d333280, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d271149, d333280, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro102992 (p : Pattern) (ha : d271155 p = 1) (hb : d333286 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d38284 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d271133 q = 1) (hb : d332889 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d271133, d332889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro102988 q ha hb
    | true =>
      simp only [d271133, d332889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro102989 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d38518 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d271134 q = 1) (hb : d332890 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d271134, d332890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d271134, d332890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d271135 q = 1) (hb : d333267 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d271135, d333267, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d271135, d333267, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d271136 q = 1) (hb : d333268 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d271136, d333268, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d271136, d333268, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d271140 q = 1) (hb : d333270 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d271140, d333270, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d271140, d333270, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro102990 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d38527 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d271141 q = 1) (hb : d333271 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d271141, d333271, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d271141, d333271, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d271142 q = 1) (hb : d333272 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d271142, d333272, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d271142, d333272, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h11 (q : Pattern) (ha : d271143 q = 1) (hb : d333273 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d271143, d333273, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d271143, d333273, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h12 (q : Pattern) (ha : d271144 q = 1) (hb : d333274 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d271144, d333274, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d271144, d333274, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d271150 q = 1) (hb : d333281 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d271150, d333281, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d271150, d333281, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro102991 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d38753 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d271151 q = 1) (hb : d333282 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d271151, d333282, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d271151, d333282, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d271152 q = 1) (hb : d333283 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d271152, d333283, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d271152, d333283, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h17 (q : Pattern) (ha : d271153 q = 1) (hb : d333284 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d271153, d333284, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d271153, d333284, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h18 (q : Pattern) (ha : d271154 q = 1) (hb : d333285 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d271154, d333285, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d271154, d333285, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h19 (q : Pattern) (ha : d271155 q = 1) (hb : d333286 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d271155, d333286, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d271155, d333286, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro102993 (p : Pattern) (ha : d271161 p = 1) (hb : d333292 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d271156 q = 1) (hb : d333287 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d271156, d333287, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d271156, d333287, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro102992 q ha hb
  have h2 (q : Pattern) (ha : d271157 q = 1) (hb : d333288 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d271157, d333288, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d271157, d333288, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d271158 q = 1) (hb : d333289 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d271158, d333289, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d271158, d333289, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d271159 q = 1) (hb : d333290 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d271159, d333290, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d271159, d333290, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d271160 q = 1) (hb : d333291 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d271160, d333291, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d271160, d333291, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d271161 q = 1) (hb : d333292 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d271161, d333292, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d271161, d333292, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro102994 (p : Pattern) (ha : d271167 p = 1) (hb : d333298 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d270027 q = 1) (hb : d333179 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d270027, d333179, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro102963 q ha hb
    | true =>
      simp only [d270027, d333179, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro102969 q ha hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d270067 q = 1) (hb : d333206 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d270067, d333206, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d270067, d333206, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro102975 q ha hb
  have h3 (q : Pattern) (ha : d270068 q = 1) (hb : d333207 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d270068, d333207, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d270068, d333207, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d270108 q = 1) (hb : d333234 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d270108, d333234, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d270108, d333234, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro102981 q ha hb
  have h5 (q : Pattern) (ha : d270109 q = 1) (hb : d333235 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d270109, d333235, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d270109, d333235, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d270110 q = 1) (hb : d333236 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d270110, d333236, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d270110, d333236, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d271119 q = 1) (hb : d333263 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d271119, d333263, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d271119, d333263, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro102987 q ha hb
  have h8 (q : Pattern) (ha : d271120 q = 1) (hb : d333264 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d271120, d333264, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d271120, d333264, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d271121 q = 1) (hb : d333265 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d271121, d333265, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d271121, d333265, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d271122 q = 1) (hb : d333266 q = 1) : d0 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d271122, d333266, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d271122, d333266, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d271162 q = 1) (hb : d333293 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d271162, d333293, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d271162, d333293, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro102993 q ha hb
  have h12 (q : Pattern) (ha : d271163 q = 1) (hb : d333294 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d271163, d333294, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d271163, d333294, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d271164 q = 1) (hb : d333295 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d271164, d333295, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d271164, d333295, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d271165 q = 1) (hb : d333296 q = 1) : d0 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d271165, d333296, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d271165, d333296, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d271166 q = 1) (hb : d333297 q = 1) : d0 q = 1 := by
    cases bit : q 10250 with
    | false =>
      simp only [d271166, d333297, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d271166, d333297, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d271167 q = 1) (hb : d333298 q = 1) : d0 q = 1 := by
    cases bit : q 260 with
    | false =>
      simp only [d271167, d333298, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d271167, d333298, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  exact h16 p ha hb
theorem andIntro102995 (p : Pattern) (ha : d271173 p = 1) (hb : d333304 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d271168 q = 1) (hb : d333299 q = 1) : d0 q = 1 := by
    cases bit : q 259 with
    | false =>
      simp only [d271168, d333299, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro102994 q ha hb
    | true =>
      simp only [d271168, d333299, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d271169 q = 1) (hb : d333300 q = 1) : d0 q = 1 := by
    cases bit : q 258 with
    | false =>
      simp only [d271169, d333300, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d271169, d333300, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d271170 q = 1) (hb : d333301 q = 1) : d0 q = 1 := by
    cases bit : q 257 with
    | false =>
      simp only [d271170, d333301, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d271170, d333301, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d271171 q = 1) (hb : d333302 q = 1) : d0 q = 1 := by
    cases bit : q 256 with
    | false =>
      simp only [d271171, d333302, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d271171, d333302, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d271172 q = 1) (hb : d333303 q = 1) : d0 q = 1 := by
    cases bit : q 255 with
    | false =>
      simp only [d271172, d333303, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d271172, d333303, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d271173 q = 1) (hb : d333304 q = 1) : d0 q = 1 := by
    cases bit : q 254 with
    | false =>
      simp only [d271173, d333304, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d271173, d333304, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro102996 (p : Pattern) (ha : d271179 p = 1) (hb : d333310 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d271174 q = 1) (hb : d333305 q = 1) : d0 q = 1 := by
    cases bit : q 253 with
    | false =>
      simp only [d271174, d333305, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro102995 q ha hb
    | true =>
      simp only [d271174, d333305, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d271175 q = 1) (hb : d333306 q = 1) : d0 q = 1 := by
    cases bit : q 252 with
    | false =>
      simp only [d271175, d333306, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d271175, d333306, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d271176 q = 1) (hb : d333307 q = 1) : d0 q = 1 := by
    cases bit : q 251 with
    | false =>
      simp only [d271176, d333307, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d271176, d333307, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d271177 q = 1) (hb : d333308 q = 1) : d0 q = 1 := by
    cases bit : q 250 with
    | false =>
      simp only [d271177, d333308, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d271177, d333308, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d271178 q = 1) (hb : d333309 q = 1) : d0 q = 1 := by
    cases bit : q 249 with
    | false =>
      simp only [d271178, d333309, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d271178, d333309, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d271179 q = 1) (hb : d333310 q = 1) : d0 q = 1 := by
    cases bit : q 245 with
    | false =>
      simp only [d271179, d333310, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d271179, d333310, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro102997 (p : Pattern) (ha : d271185 p = 1) (hb : d333316 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d271180 q = 1) (hb : d333311 q = 1) : d0 q = 1 := by
    cases bit : q 200 with
    | false =>
      simp only [d271180, d333311, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro102996 q ha hb
    | true =>
      simp only [d271180, d333311, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d271181 q = 1) (hb : d333312 q = 1) : d0 q = 1 := by
    cases bit : q 199 with
    | false =>
      simp only [d271181, d333312, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d271181, d333312, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d271182 q = 1) (hb : d333313 q = 1) : d0 q = 1 := by
    cases bit : q 186 with
    | false =>
      simp only [d271182, d333313, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d271182, d333313, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d271183 q = 1) (hb : d333314 q = 1) : d0 q = 1 := by
    cases bit : q 185 with
    | false =>
      simp only [d271183, d333314, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d271183, d333314, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d271184 q = 1) (hb : d333315 q = 1) : d0 q = 1 := by
    cases bit : q 184 with
    | false =>
      simp only [d271184, d333315, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d271184, d333315, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d271185 q = 1) (hb : d333316 q = 1) : d0 q = 1 := by
    cases bit : q 181 with
    | false =>
      simp only [d271185, d333316, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d271185, d333316, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro102998 (p : Pattern) (ha : d271191 p = 1) (hb : d333322 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d271186 q = 1) (hb : d333317 q = 1) : d0 q = 1 := by
    cases bit : q 177 with
    | false =>
      simp only [d271186, d333317, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro102997 q ha hb
    | true =>
      simp only [d271186, d333317, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d271187 q = 1) (hb : d333318 q = 1) : d0 q = 1 := by
    cases bit : q 164 with
    | false =>
      simp only [d271187, d333318, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d271187, d333318, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d271188 q = 1) (hb : d333319 q = 1) : d0 q = 1 := by
    cases bit : q 156 with
    | false =>
      simp only [d271188, d333319, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d271188, d333319, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d271189 q = 1) (hb : d333320 q = 1) : d0 q = 1 := by
    cases bit : q 155 with
    | false =>
      simp only [d271189, d333320, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d271189, d333320, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d271190 q = 1) (hb : d333321 q = 1) : d0 q = 1 := by
    cases bit : q 134 with
    | false =>
      simp only [d271190, d333321, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d271190, d333321, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d271191 q = 1) (hb : d333322 q = 1) : d0 q = 1 := by
    cases bit : q 133 with
    | false =>
      simp only [d271191, d333322, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d271191, d333322, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro102999 (p : Pattern) (ha : d271197 p = 1) (hb : d333328 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d271192 q = 1) (hb : d333323 q = 1) : d0 q = 1 := by
    cases bit : q 120 with
    | false =>
      simp only [d271192, d333323, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro102998 q ha hb
    | true =>
      simp only [d271192, d333323, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d271193 q = 1) (hb : d333324 q = 1) : d0 q = 1 := by
    cases bit : q 118 with
    | false =>
      simp only [d271193, d333324, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d271193, d333324, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d271194 q = 1) (hb : d333325 q = 1) : d0 q = 1 := by
    cases bit : q 114 with
    | false =>
      simp only [d271194, d333325, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d271194, d333325, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d271195 q = 1) (hb : d333326 q = 1) : d0 q = 1 := by
    cases bit : q 111 with
    | false =>
      simp only [d271195, d333326, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d271195, d333326, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d271196 q = 1) (hb : d333327 q = 1) : d0 q = 1 := by
    cases bit : q 98 with
    | false =>
      simp only [d271196, d333327, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d271196, d333327, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d271197 q = 1) (hb : d333328 q = 1) : d0 q = 1 := by
    cases bit : q 97 with
    | false =>
      simp only [d271197, d333328, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d271197, d333328, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
end NetHack.Soko22Hazard87
