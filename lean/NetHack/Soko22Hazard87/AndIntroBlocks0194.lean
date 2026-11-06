import NetHack.Soko22Hazard87.AndIntroBlocks0193
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Soko22Hazard87
open NetHack.Sokoban NetHack.Sokoban.PatternCorrection
theorem andIntro48500 (p : Pattern) (ha : d205450 p = 1) (hb : d207005 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d205436 q = 1) (hb : d206991 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d205436, d206991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48473 q ha hb
    | true =>
      simp only [d205436, d206991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d205437 q = 1) (hb : d206992 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d205437, d206992, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d205437, d206992, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d205438 q = 1) (hb : d206993 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d205438, d206993, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d205438, d206993, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d205439 q = 1) (hb : d206994 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d205439, d206994, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d205439, d206994, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d205440 q = 1) (hb : d206995 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d205440, d206995, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d205440, d206995, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d205450 q = 1) (hb : d207005 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d205450, d207005, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d205450, d207005, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro48501 (p : Pattern) (ha : d205474 p = 1) (hb : d207012 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d205459 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d205460 q = 1) (hb : d206694 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d205460, d206694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d205460, d206694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48451 q ha hb
  have h3 (q : Pattern) (ha : d205266 q = 1) (hb : d206585 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d205266, d206585, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48451 q ha hb
    | true =>
      simp only [d205266, d206585, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h4 (q : Pattern) (ha : d205461 q = 1) (hb : d206695 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d205461, d206695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d205461, d206695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d205267 q = 1) (hb : d206586 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d205267, d206586, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d205267, d206586, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h6 (q : Pattern) (ha : d205462 q = 1) (hb : d206696 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d205462, d206696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d205462, d206696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d205463 q = 1) (hb : d206697 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d205463, d206697, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d205463, d206697, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h8 (q : Pattern) (ha : d205464 q = 1) (hb : d207011 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d205464, d207011, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d205464, d207011, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d205473 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d205474 q = 1) (hb : d207012 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d205474, d207012, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d205474, d207012, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
  exact h10 p ha hb
theorem andIntro48502 (p : Pattern) (ha : d205485 p = 1) (hb : d207018 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d205460 q = 1) (hb : d206694 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d205460, d206694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d205460, d206694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48451 q ha hb
  have h2 (q : Pattern) (ha : d205266 q = 1) (hb : d206585 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d205266, d206585, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48451 q ha hb
    | true =>
      simp only [d205266, d206585, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d205461 q = 1) (hb : d206695 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d205461, d206695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d205461, d206695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d205267 q = 1) (hb : d206586 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d205267, d206586, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d205267, d206586, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d205462 q = 1) (hb : d206696 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d205462, d206696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d205462, d206696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d205463 q = 1) (hb : d206697 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d205463, d206697, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d205463, d206697, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d205475 q = 1) (hb : d207013 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d205475, d207013, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d205475, d207013, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48455 q ha hb
  have h8 (q : Pattern) (ha : d205280 q = 1) (hb : d206813 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d205280, d206813, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48455 q ha hb
    | true =>
      simp only [d205280, d206813, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d205476 q = 1) (hb : d207014 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d205476, d207014, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d205476, d207014, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d205281 q = 1) (hb : d206814 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d205281, d206814, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d205281, d206814, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h11 (q : Pattern) (ha : d205477 q = 1) (hb : d207015 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d205477, d207015, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d205477, d207015, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d205478 q = 1) (hb : d207016 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d205478, d207016, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d205478, d207016, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d205479 q = 1) (hb : d207017 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d205479, d207017, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d205479, d207017, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d205472 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d205480 q = 1) (hb : d206411 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d205480, d206411, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d205480, d206411, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48457 q ha hb
  have h16 (q : Pattern) (ha : d205295 q = 1) (hb : d206324 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d205295, d206324, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48457 q ha hb
    | true =>
      simp only [d205295, d206324, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h17 (q : Pattern) (ha : d205481 q = 1) (hb : d206412 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d205481, d206412, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d205481, d206412, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d205296 q = 1) (hb : d206325 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d205296, d206325, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d205296, d206325, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h19 (q : Pattern) (ha : d205482 q = 1) (hb : d206413 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d205482, d206413, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d205482, d206413, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d205483 q = 1) (hb : d206414 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d205483, d206414, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d205483, d206414, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h21 (q : Pattern) (ha : d205484 q = 1) (hb : d206699 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d205484, d206699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
    | true =>
      simp only [d205484, d206699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
  have h22 (q : Pattern) (ha : d205485 q = 1) (hb : d207018 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d205485, d207018, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d205485, d207018, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
  exact h22 p ha hb
theorem andIntro48503 (p : Pattern) (ha : d205490 p = 1) (hb : d207028 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d205469 q = 1) (hb : d207022 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d205469, d207022, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d205469, d207022, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48483 q ha hb
  have h2 (q : Pattern) (ha : d205286 q = 1) (hb : d206918 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d205286, d206918, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48483 q ha hb
    | true =>
      simp only [d205286, d206918, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d205470 q = 1) (hb : d207023 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d205470, d207023, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d205470, d207023, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d205287 q = 1) (hb : d206919 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d205287, d206919, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d205287, d206919, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d205471 q = 1) (hb : d207024 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d205471, d207024, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d205471, d207024, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d205472 q = 1) (hb : d207025 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d205472, d207025, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d205472, d207025, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d205480 q = 1) (hb : d206411 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d205480, d206411, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d205480, d206411, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48457 q ha hb
  have h8 (q : Pattern) (ha : d205295 q = 1) (hb : d206324 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d205295, d206324, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48457 q ha hb
    | true =>
      simp only [d205295, d206324, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d205481 q = 1) (hb : d206412 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d205481, d206412, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d205481, d206412, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d205296 q = 1) (hb : d206325 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d205296, d206325, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d205296, d206325, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h11 (q : Pattern) (ha : d205482 q = 1) (hb : d206413 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d205482, d206413, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d205482, d206413, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d205483 q = 1) (hb : d206414 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d205483, d206414, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d205483, d206414, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d205484 q = 1) (hb : d207026 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d205484, d207026, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d205484, d207026, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d205489 q = 1) (hb : d207027 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d205489, d207027, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d205489, d207027, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h15 (q : Pattern) (ha : d205490 q = 1) (hb : d207028 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d205490, d207028, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d205490, d207028, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro48504 (p : Pattern) (ha : d205496 p = 1) (hb : d207038 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d205475 q = 1) (hb : d207013 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d205475, d207013, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d205475, d207013, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48455 q ha hb
  have h2 (q : Pattern) (ha : d205280 q = 1) (hb : d206813 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d205280, d206813, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48455 q ha hb
    | true =>
      simp only [d205280, d206813, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d205476 q = 1) (hb : d207014 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d205476, d207014, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d205476, d207014, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d205281 q = 1) (hb : d206814 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d205281, d206814, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d205281, d206814, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d205477 q = 1) (hb : d207015 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d205477, d207015, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d205477, d207015, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d205478 q = 1) (hb : d207016 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d205478, d207016, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d205478, d207016, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d205480 q = 1) (hb : d207033 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d205480, d207033, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d205480, d207033, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48461 q ha hb
  have h8 (q : Pattern) (ha : d205295 q = 1) (hb : d206825 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d205295, d206825, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48461 q ha hb
    | true =>
      simp only [d205295, d206825, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d205481 q = 1) (hb : d207034 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d205481, d207034, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d205481, d207034, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d205296 q = 1) (hb : d206826 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d205296, d206826, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d205296, d206826, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h11 (q : Pattern) (ha : d205482 q = 1) (hb : d207035 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d205482, d207035, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d205482, d207035, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d205483 q = 1) (hb : d207036 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d205483, d207036, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d205483, d207036, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d205495 q = 1) (hb : d207037 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d205495, d207037, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d205495, d207037, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d205480 q = 1) (hb : d206411 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d205480, d206411, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d205480, d206411, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48457 q ha hb
  have h15 (q : Pattern) (ha : d205295 q = 1) (hb : d206324 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d205295, d206324, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48457 q ha hb
    | true =>
      simp only [d205295, d206324, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h16 (q : Pattern) (ha : d205481 q = 1) (hb : d206412 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d205481, d206412, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d205481, d206412, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d205296 q = 1) (hb : d206325 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d205296, d206325, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d205296, d206325, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h18 (q : Pattern) (ha : d205482 q = 1) (hb : d206413 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d205482, d206413, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d205482, d206413, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d205483 q = 1) (hb : d206414 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d205483, d206414, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d205483, d206414, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h20 (q : Pattern) (ha : d205489 q = 1) (hb : d207027 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d205489, d207027, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d205489, d207027, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h21 (q : Pattern) (ha : d205496 q = 1) (hb : d207038 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d205496, d207038, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d205496, d207038, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
  exact h21 p ha hb
theorem andIntro48505 (p : Pattern) (ha : d205500 p = 1) (hb : d207047 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d205480 q = 1) (hb : d207042 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d205480, d207042, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d205480, d207042, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48464 q ha hb
  have h2 (q : Pattern) (ha : d205295 q = 1) (hb : d206841 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d205295, d206841, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48464 q ha hb
    | true =>
      simp only [d205295, d206841, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d205481 q = 1) (hb : d207043 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d205481, d207043, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d205481, d207043, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d205296 q = 1) (hb : d206842 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d205296, d206842, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d205296, d206842, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d205482 q = 1) (hb : d207044 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d205482, d207044, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d205482, d207044, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d205483 q = 1) (hb : d207045 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d205483, d207045, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d205483, d207045, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d205489 q = 1) (hb : d207046 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d205489, d207046, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d205489, d207046, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d205500 q = 1) (hb : d207047 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d205500, d207047, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d205500, d207047, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro48506 (p : Pattern) (ha : d205506 p = 1) (hb : d207053 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d205486 q = 1) (hb : d207019 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d205486, d207019, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48501 q ha hb
    | true =>
      simp only [d205486, d207019, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48502 q ha hb
  have h2 (q : Pattern) (ha : d205487 q = 1) (hb : d207020 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d205487, d207020, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d205487, d207020, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d205488 q = 1) (hb : d207021 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d205488, d207021, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d205488, d207021, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d205491 q = 1) (hb : d207029 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d205491, d207029, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48502 q ha hb
    | true =>
      simp only [d205491, d207029, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48503 q ha hb
  have h5 (q : Pattern) (ha : d205492 q = 1) (hb : d207030 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d205492, d207030, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d205492, d207030, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d205493 q = 1) (hb : d207031 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d205493, d207031, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d205493, d207031, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d205494 q = 1) (hb : d207032 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d205494, d207032, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d205494, d207032, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d205497 q = 1) (hb : d207039 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d205497, d207039, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48502 q ha hb
    | true =>
      simp only [d205497, d207039, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48504 q ha hb
  have h9 (q : Pattern) (ha : d205498 q = 1) (hb : d207040 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d205498, d207040, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d205498, d207040, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d205499 q = 1) (hb : d207041 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d205499, d207041, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d205499, d207041, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d205501 q = 1) (hb : d207048 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d205501, d207048, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48504 q ha hb
    | true =>
      simp only [d205501, d207048, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48505 q ha hb
  have h12 (q : Pattern) (ha : d205502 q = 1) (hb : d207049 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d205502, d207049, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d205502, d207049, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d205503 q = 1) (hb : d207050 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d205503, d207050, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d205503, d207050, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d205504 q = 1) (hb : d207051 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d205504, d207051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d205504, d207051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d205505 q = 1) (hb : d207052 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d205505, d207052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d205505, d207052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d205506 q = 1) (hb : d207053 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d205506, d207053, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d205506, d207053, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h16 p ha hb
theorem andIntro48507 (p : Pattern) (ha : d205511 p = 1) (hb : d207058 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d205497 q = 1) (hb : d207039 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d205497, d207039, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48502 q ha hb
    | true =>
      simp only [d205497, d207039, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48504 q ha hb
  have h2 (q : Pattern) (ha : d205498 q = 1) (hb : d207040 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d205498, d207040, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d205498, d207040, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d205499 q = 1) (hb : d207041 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d205499, d207041, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d205499, d207041, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d205501 q = 1) (hb : d207048 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d205501, d207048, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48504 q ha hb
    | true =>
      simp only [d205501, d207048, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48505 q ha hb
  have h5 (q : Pattern) (ha : d205502 q = 1) (hb : d207049 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d205502, d207049, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d205502, d207049, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d205503 q = 1) (hb : d207050 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d205503, d207050, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d205503, d207050, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d205504 q = 1) (hb : d207051 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d205504, d207051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d205504, d207051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d205509 q = 1) (hb : d207056 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d205509, d207056, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d205509, d207056, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d205510 q = 1) (hb : d207057 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d205510, d207057, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d205510, d207057, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d205511 q = 1) (hb : d207058 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d205511, d207058, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d205511, d207058, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h10 p ha hb
theorem andIntro48508 (p : Pattern) (ha : d205517 p = 1) (hb : d207064 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d205507 q = 1) (hb : d207054 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d205507, d207054, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48506 q ha hb
    | true =>
      simp only [d205507, d207054, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d205508 q = 1) (hb : d207055 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d205508, d207055, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d205508, d207055, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d205512 q = 1) (hb : d207059 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d205512, d207059, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48507 q ha hb
    | true =>
      simp only [d205512, d207059, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d205513 q = 1) (hb : d207060 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d205513, d207060, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d205513, d207060, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d205514 q = 1) (hb : d207061 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d205514, d207061, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d205514, d207061, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d205515 q = 1) (hb : d207062 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d205515, d207062, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d205515, d207062, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d205516 q = 1) (hb : d207063 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d205516, d207063, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d205516, d207063, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d205517 q = 1) (hb : d207064 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d205517, d207064, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d205517, d207064, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro48509 (p : Pattern) (ha : d205500 p = 1) (hb : d207066 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d205480 q = 1) (hb : d207033 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d205480, d207033, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d205480, d207033, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48461 q ha hb
  have h2 (q : Pattern) (ha : d205295 q = 1) (hb : d206825 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d205295, d206825, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48461 q ha hb
    | true =>
      simp only [d205295, d206825, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d205481 q = 1) (hb : d207034 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d205481, d207034, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d205481, d207034, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d205296 q = 1) (hb : d206826 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d205296, d206826, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d205296, d206826, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d205482 q = 1) (hb : d207035 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d205482, d207035, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d205482, d207035, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d205483 q = 1) (hb : d207036 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d205483, d207036, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d205483, d207036, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d205489 q = 1) (hb : d207065 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d205489, d207065, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d205489, d207065, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d205500 q = 1) (hb : d207066 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d205500, d207066, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d205500, d207066, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro48510 (p : Pattern) (ha : d205519 p = 1) (hb : d207072 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d205501 q = 1) (hb : d207067 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d205501, d207067, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48504 q ha hb
    | true =>
      simp only [d205501, d207067, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48509 q ha hb
  have h2 (q : Pattern) (ha : d205502 q = 1) (hb : d207068 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d205502, d207068, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d205502, d207068, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d205503 q = 1) (hb : d207069 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d205503, d207069, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d205503, d207069, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d205509 q = 1) (hb : d207070 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d205509, d207070, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d205509, d207070, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d205518 q = 1) (hb : d207071 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d205518, d207071, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d205518, d207071, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d205519 q = 1) (hb : d207072 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d205519, d207072, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d205519, d207072, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro48511 (p : Pattern) (ha : d205525 p = 1) (hb : d207078 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d205512 q = 1) (hb : d207059 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d205512, d207059, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48507 q ha hb
    | true =>
      simp only [d205512, d207059, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d205513 q = 1) (hb : d207060 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d205513, d207060, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d205513, d207060, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d205520 q = 1) (hb : d207073 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d205520, d207073, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48510 q ha hb
    | true =>
      simp only [d205520, d207073, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d205521 q = 1) (hb : d207074 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d205521, d207074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d205521, d207074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d205522 q = 1) (hb : d207075 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d205522, d207075, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d205522, d207075, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d205523 q = 1) (hb : d207076 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d205523, d207076, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d205523, d207076, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d205524 q = 1) (hb : d207077 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d205524, d207077, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d205524, d207077, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d205525 q = 1) (hb : d207078 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d205525, d207078, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d205525, d207078, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro48512 (p : Pattern) (ha : d205511 p = 1) (hb : d207082 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d205497 q = 1) (hb : d207039 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d205497, d207039, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48502 q ha hb
    | true =>
      simp only [d205497, d207039, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48504 q ha hb
  have h2 (q : Pattern) (ha : d205498 q = 1) (hb : d207040 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d205498, d207040, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d205498, d207040, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d205499 q = 1) (hb : d207041 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d205499, d207041, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d205499, d207041, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d205501 q = 1) (hb : d207048 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d205501, d207048, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48504 q ha hb
    | true =>
      simp only [d205501, d207048, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48505 q ha hb
  have h5 (q : Pattern) (ha : d205502 q = 1) (hb : d207049 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d205502, d207049, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d205502, d207049, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d205503 q = 1) (hb : d207050 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d205503, d207050, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d205503, d207050, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d205504 q = 1) (hb : d207051 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d205504, d207051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d205504, d207051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d205501 q = 1) (hb : d207067 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d205501, d207067, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48504 q ha hb
    | true =>
      simp only [d205501, d207067, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48509 q ha hb
  have h9 (q : Pattern) (ha : d205502 q = 1) (hb : d207068 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d205502, d207068, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d205502, d207068, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d205503 q = 1) (hb : d207069 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d205503, d207069, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d205503, d207069, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d205509 q = 1) (hb : d207070 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d205509, d207070, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d205509, d207070, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d205510 q = 1) (hb : d207081 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d205510, d207081, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d205510, d207081, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d205511 q = 1) (hb : d207082 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d205511, d207082, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d205511, d207082, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h13 p ha hb
theorem andIntro48513 (p : Pattern) (ha : d205536 p = 1) (hb : d207088 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d205512 q = 1) (hb : d207083 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d205512, d207083, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48512 q ha hb
    | true =>
      simp only [d205512, d207083, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d205513 q = 1) (hb : d207084 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d205513, d207084, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d205513, d207084, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d205533 q = 1) (hb : d207085 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d205533, d207085, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d205533, d207085, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d205534 q = 1) (hb : d207086 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d205534, d207086, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d205534, d207086, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d205535 q = 1) (hb : d207087 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d205535, d207087, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d205535, d207087, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d205536 q = 1) (hb : d207088 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d205536, d207088, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d205536, d207088, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro48514 (p : Pattern) (ha : d205542 p = 1) (hb : d207094 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d205526 q = 1) (hb : d207079 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d205526, d207079, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48508 q ha hb
    | true =>
      simp only [d205526, d207079, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48511 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d205531 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d205532 q = 1) (hb : d207080 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d205532, d207080, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d205532, d207080, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d205537 q = 1) (hb : d207089 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d205537, d207089, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48513 q ha hb
    | true =>
      simp only [d205537, d207089, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d205538 q = 1) (hb : d207090 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d205538, d207090, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d205538, d207090, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d205539 q = 1) (hb : d207091 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d205539, d207091, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d205539, d207091, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d205540 q = 1) (hb : d207092 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d205540, d207092, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d205540, d207092, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d205541 q = 1) (hb : d207093 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d205541, d207093, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d205541, d207093, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d205542 q = 1) (hb : d207094 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d205542, d207094, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d205542, d207094, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro48515 (p : Pattern) (ha : d205530 p = 1) (hb : d207099 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d205520 q = 1) (hb : d207073 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d205520, d207073, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48510 q ha hb
    | true =>
      simp only [d205520, d207073, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d205521 q = 1) (hb : d207074 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d205521, d207074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d205521, d207074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d205527 q = 1) (hb : d207096 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d205527, d207096, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d205527, d207096, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d205528 q = 1) (hb : d207097 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d205528, d207097, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d205528, d207097, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d205529 q = 1) (hb : d207098 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d205529, d207098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d205529, d207098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d205530 q = 1) (hb : d207099 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d205530, d207099, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d205530, d207099, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro48516 (p : Pattern) (ha : d205549 p = 1) (hb : d207105 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d205544 q = 1) (hb : d207100 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d205544, d207100, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48515 q ha hb
    | true =>
      simp only [d205544, d207100, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d205545 q = 1) (hb : d207101 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d205545, d207101, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d205545, d207101, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d205546 q = 1) (hb : d207102 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d205546, d207102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d205546, d207102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d205547 q = 1) (hb : d207103 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d205547, d207103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d205547, d207103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d205548 q = 1) (hb : d207104 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d205548, d207104, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d205548, d207104, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d205549 q = 1) (hb : d207105 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d205549, d207105, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d205549, d207105, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro48517 (p : Pattern) (ha : d205555 p = 1) (hb : d207111 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d205335 q = 1) (hb : d206879 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d205335, d206879, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d205335, d206879, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48471 q ha hb
  have h2 (q : Pattern) (ha : d205336 q = 1) (hb : d206880 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d205336, d206880, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d205336, d206880, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d205345 q = 1) (hb : d206889 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d205345, d206889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48471 q ha hb
    | true =>
      simp only [d205345, d206889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48474 q ha hb
  have h4 (q : Pattern) (ha : d205346 q = 1) (hb : d206890 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d205346, d206890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d205346, d206890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d205347 q = 1) (hb : d206891 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d205347, d206891, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d205347, d206891, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d205429 q = 1) (hb : d206979 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d205429, d206979, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48488 q ha hb
    | true =>
      simp only [d205429, d206979, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48496 q ha hb
  have h7 (q : Pattern) (ha : d205442 q = 1) (hb : d206997 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d205442, d206997, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48497 q ha hb
    | true =>
      simp only [d205442, d206997, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48498 q ha hb
  have h8 (q : Pattern) (ha : d205443 q = 1) (hb : d206998 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d205443, d206998, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d205443, d206998, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d205444 q = 1) (hb : d206999 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d205444, d206999, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d205444, d206999, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h10 (q : Pattern) (ha : d205445 q = 1) (hb : d207000 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d205445, d207000, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d205445, d207000, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d205449 q = 1) (hb : d207004 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d205449, d207004, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d205449, d207004, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48499 q ha hb
  have h12 (q : Pattern) (ha : d205451 q = 1) (hb : d207006 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d205451, d207006, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d205451, d207006, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48500 q ha hb
  have h13 (q : Pattern) (ha : d205452 q = 1) (hb : d207007 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d205452, d207007, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d205452, d207007, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d205453 q = 1) (hb : d207008 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d205453, d207008, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d205453, d207008, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h15 (q : Pattern) (ha : d205454 q = 1) (hb : d207009 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d205454, d207009, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d205454, d207009, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h16 (q : Pattern) (ha : d205455 q = 1) (hb : d207010 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d205455, d207010, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d205455, d207010, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d205543 q = 1) (hb : d207095 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d205543, d207095, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d205543, d207095, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48514 q ha hb
  have h18 (q : Pattern) (ha : d205550 q = 1) (hb : d207106 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d205550, d207106, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d205550, d207106, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48516 q ha hb
  have h19 (q : Pattern) (ha : d205551 q = 1) (hb : d207107 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d205551, d207107, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d205551, d207107, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d205552 q = 1) (hb : d207108 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d205552, d207108, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d205552, d207108, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h21 (q : Pattern) (ha : d205553 q = 1) (hb : d207109 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d205553, d207109, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d205553, d207109, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h22 (q : Pattern) (ha : d205554 q = 1) (hb : d207110 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d205554, d207110, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d205554, d207110, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h23 (q : Pattern) (ha : d205555 q = 1) (hb : d207111 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d205555, d207111, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d205555, d207111, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
  exact h23 p ha hb
theorem andIntro48518 (p : Pattern) (ha : d205561 p = 1) (hb : d207117 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d205556 q = 1) (hb : d207112 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d205556, d207112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d205556, d207112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48517 q ha hb
  have h2 (q : Pattern) (ha : d205557 q = 1) (hb : d207113 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d205557, d207113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d205557, d207113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d205558 q = 1) (hb : d207114 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d205558, d207114, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d205558, d207114, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d205559 q = 1) (hb : d207115 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d205559, d207115, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d205559, d207115, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d205560 q = 1) (hb : d207116 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d205560, d207116, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d205560, d207116, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d205561 q = 1) (hb : d207117 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d205561, d207117, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d205561, d207117, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro48519 (p : Pattern) (ha : d10054 p = 1) (hb : d53285 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d13 q = 1) (hb : d127 q = 1) : d0 q = 1 := by
    cases bit : q 248 with
    | false =>
      simp only [d13, d127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d13, d127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d308 q = 1) (hb : d52107 q = 1) : d0 q = 1 := by
    cases bit : q 247 with
    | false =>
      simp only [d308, d52107, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d308, d52107, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d1523 q = 1) (hb : d52964 q = 1) : d0 q = 1 := by
    cases bit : q 246 with
    | false =>
      simp only [d1523, d52964, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1523, d52964, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d2005 q = 1) (hb : d53284 q = 1) : d0 q = 1 := by
    cases bit : q 226 with
    | false =>
      simp only [d2005, d53284, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d2005, d53284, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d2006 q = 1) (hb : d53285 q = 1) : d0 q = 1 := by
    cases bit : q 225 with
    | false =>
      simp only [d2006, d53285, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d2006, d53285, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d53285 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d10054 q = 1) (hb : d53285 q = 1) : d0 q = 1 := by
    cases bit : q 224 with
    | false =>
      simp only [d10054, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d10054, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro48520 (p : Pattern) (ha : d32687 p = 1) (hb : d53278 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d13 q = 1) (hb : d127 q = 1) : d0 q = 1 := by
    cases bit : q 248 with
    | false =>
      simp only [d13, d127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d13, d127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d307 q = 1) (hb : d52106 q = 1) : d0 q = 1 := by
    cases bit : q 247 with
    | false =>
      simp only [d307, d52106, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d307, d52106, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d1997 q = 1) (hb : d53276 q = 1) : d0 q = 1 := by
    cases bit : q 246 with
    | false =>
      simp only [d1997, d53276, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d1997, d53276, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d1998 q = 1) (hb : d53277 q = 1) : d0 q = 1 := by
    cases bit : q 226 with
    | false =>
      simp only [d1998, d53277, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1998, d53277, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d1999 q = 1) (hb : d53278 q = 1) : d0 q = 1 := by
    cases bit : q 225 with
    | false =>
      simp only [d1999, d53278, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1999, d53278, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d53278 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d32687 q = 1) (hb : d53278 q = 1) : d0 q = 1 := by
    cases bit : q 224 with
    | false =>
      simp only [d32687, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d32687, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro48521 (p : Pattern) (ha : d32698 p = 1) (hb : d53281 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d13 q = 1) (hb : d127 q = 1) : d0 q = 1 := by
    cases bit : q 248 with
    | false =>
      simp only [d13, d127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d13, d127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d308 q = 1) (hb : d52107 q = 1) : d0 q = 1 := by
    cases bit : q 247 with
    | false =>
      simp only [d308, d52107, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d308, d52107, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d1523 q = 1) (hb : d52964 q = 1) : d0 q = 1 := by
    cases bit : q 246 with
    | false =>
      simp only [d1523, d52964, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1523, d52964, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d2001 q = 1) (hb : d53280 q = 1) : d0 q = 1 := by
    cases bit : q 226 with
    | false =>
      simp only [d2001, d53280, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2001, d53280, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d2002 q = 1) (hb : d53281 q = 1) : d0 q = 1 := by
    cases bit : q 225 with
    | false =>
      simp only [d2002, d53281, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d2002, d53281, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d53281 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d32698 q = 1) (hb : d53281 q = 1) : d0 q = 1 := by
    cases bit : q 224 with
    | false =>
      simp only [d32698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d32698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro48522 (p : Pattern) (ha : d205581 p = 1) (hb : d207125 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d205568 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d32699 q = 1) (hb : d205566 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d32699, d205566, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48520 q ha hb
    | true =>
      simp only [d32699, d205566, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48521 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d10055 q = 1) (hb : d205567 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d10055, d205567, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d10055, d205567, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48519 q ha hb
  have h4 (q : Pattern) (ha : d32700 q = 1) (hb : d205568 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d32700, d205568, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d32700, d205568, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d205568 q = 1) (hb : d207122 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d207122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d207122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d205569 q = 1) (hb : d207123 q = 1) : d0 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d205569, d207123, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d205569, d207123, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h7 (q : Pattern) (ha : d205570 q = 1) (hb : d207124 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d205570, d207124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d205570, d207124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d205580 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d205581 q = 1) (hb : d207125 q = 1) : d0 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d205581, d207125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d205581, d207125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  exact h9 p ha hb
theorem andIntro48523 (p : Pattern) (ha : d205593 p = 1) (hb : d207131 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d205575 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d205582 q = 1) (hb : d207126 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d205582, d207126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48522 q ha hb
    | true =>
      simp only [d205582, d207126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d205583 q = 1) (hb : d207127 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d205583, d207127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d205583, d207127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h4 (q : Pattern) (ha : d205584 q = 1) (hb : d207128 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d205584, d207128, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d205584, d207128, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d205585 q = 1) (hb : d207129 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d205585, d207129, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d205585, d207129, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h6 (q : Pattern) (ha : d205586 q = 1) (hb : d207130 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d205586, d207130, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d205586, d207130, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d0 q = 1) (hb : d205592 q = 1) : d0 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d205593 q = 1) (hb : d207131 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d205593, d207131, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d205593, d207131, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
  exact h8 p ha hb
theorem andIntro48524 (p : Pattern) (ha : d2040 p = 1) (hb : d53297 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d13 q = 1) (hb : d127 q = 1) : d0 q = 1 := by
    cases bit : q 248 with
    | false =>
      simp only [d13, d127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d13, d127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d307 q = 1) (hb : d52106 q = 1) : d0 q = 1 := by
    cases bit : q 247 with
    | false =>
      simp only [d307, d52106, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d307, d52106, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d1997 q = 1) (hb : d53276 q = 1) : d0 q = 1 := by
    cases bit : q 246 with
    | false =>
      simp only [d1997, d53276, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d1997, d53276, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d128 q = 1) (hb : d51979 q = 1) : d0 q = 1 := by
    cases bit : q 247 with
    | false =>
      simp only [d128, d51979, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d128, d51979, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h5 (q : Pattern) (ha : d2016 q = 1) (hb : d53295 q = 1) : d0 q = 1 := by
    cases bit : q 246 with
    | false =>
      simp only [d2016, d53295, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d2016, d53295, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d2017 q = 1) (hb : d53296 q = 1) : d0 q = 1 := by
    cases bit : q 226 with
    | false =>
      simp only [d2017, d53296, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d2017, d53296, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d2018 q = 1) (hb : d53297 q = 1) : d0 q = 1 := by
    cases bit : q 225 with
    | false =>
      simp only [d2018, d53297, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d2018, d53297, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d53297 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d2040 q = 1) (hb : d53297 q = 1) : d0 q = 1 := by
    cases bit : q 224 with
    | false =>
      simp only [d2040, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d2040, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro48525 (p : Pattern) (ha : d2042 p = 1) (hb : d53301 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d13 q = 1) (hb : d127 q = 1) : d0 q = 1 := by
    cases bit : q 248 with
    | false =>
      simp only [d13, d127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d13, d127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d128 q = 1) (hb : d51979 q = 1) : d0 q = 1 := by
    cases bit : q 247 with
    | false =>
      simp only [d128, d51979, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d128, d51979, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d2016 q = 1) (hb : d53295 q = 1) : d0 q = 1 := by
    cases bit : q 246 with
    | false =>
      simp only [d2016, d53295, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d2016, d53295, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d2021 q = 1) (hb : d53300 q = 1) : d0 q = 1 := by
    cases bit : q 226 with
    | false =>
      simp only [d2021, d53300, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d2021, d53300, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d2022 q = 1) (hb : d53301 q = 1) : d0 q = 1 := by
    cases bit : q 225 with
    | false =>
      simp only [d2022, d53301, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d2022, d53301, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d53301 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d2042 q = 1) (hb : d53301 q = 1) : d0 q = 1 := by
    cases bit : q 224 with
    | false =>
      simp only [d2042, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d2042, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro48526 (p : Pattern) (ha : d2046 p = 1) (hb : d53306 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d13 q = 1) (hb : d127 q = 1) : d0 q = 1 := by
    cases bit : q 248 with
    | false =>
      simp only [d13, d127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d13, d127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d307 q = 1) (hb : d52106 q = 1) : d0 q = 1 := by
    cases bit : q 247 with
    | false =>
      simp only [d307, d52106, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d307, d52106, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d1997 q = 1) (hb : d53276 q = 1) : d0 q = 1 := by
    cases bit : q 246 with
    | false =>
      simp only [d1997, d53276, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d1997, d53276, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d2013 q = 1) (hb : d53292 q = 1) : d0 q = 1 := by
    cases bit : q 226 with
    | false =>
      simp only [d2013, d53292, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d2013, d53292, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d2027 q = 1) (hb : d53306 q = 1) : d0 q = 1 := by
    cases bit : q 225 with
    | false =>
      simp only [d2027, d53306, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d2027, d53306, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d53306 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d2046 q = 1) (hb : d53306 q = 1) : d0 q = 1 := by
    cases bit : q 224 with
    | false =>
      simp only [d2046, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d2046, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro48527 (p : Pattern) (ha : d32701 p = 1) (hb : d53293 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d13 q = 1) (hb : d127 q = 1) : d0 q = 1 := by
    cases bit : q 248 with
    | false =>
      simp only [d13, d127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d13, d127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d307 q = 1) (hb : d52106 q = 1) : d0 q = 1 := by
    cases bit : q 247 with
    | false =>
      simp only [d307, d52106, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d307, d52106, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d1997 q = 1) (hb : d53276 q = 1) : d0 q = 1 := by
    cases bit : q 246 with
    | false =>
      simp only [d1997, d53276, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d1997, d53276, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d1998 q = 1) (hb : d53277 q = 1) : d0 q = 1 := by
    cases bit : q 226 with
    | false =>
      simp only [d1998, d53277, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1998, d53277, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d2013 q = 1) (hb : d53292 q = 1) : d0 q = 1 := by
    cases bit : q 226 with
    | false =>
      simp only [d2013, d53292, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d2013, d53292, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d2014 q = 1) (hb : d53293 q = 1) : d0 q = 1 := by
    cases bit : q 225 with
    | false =>
      simp only [d2014, d53293, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d2014, d53293, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d0 q = 1) (hb : d53293 q = 1) : d0 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d32701 q = 1) (hb : d53293 q = 1) : d0 q = 1 := by
    cases bit : q 224 with
    | false =>
      simp only [d32701, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d32701, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro48528 (p : Pattern) (ha : d205598 p = 1) (hb : d207137 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d205578 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d205576 q = 1) (hb : d207132 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d205576, d207132, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48527 q hb ha
    | true =>
      simp only [d205576, d207132, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48524 q hb ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d2043 q = 1) (hb : d205577 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d2043, d205577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d2043, d205577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48525 q ha hb
  have h4 (q : Pattern) (ha : d205578 q = 1) (hb : d207133 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d205578, d207133, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d205578, d207133, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d205578 q = 1) (hb : d207134 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d207134, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d207134, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d205595 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d2047 q = 1) (hb : d205594 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d2047, d205594, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48526 q ha hb
    | true =>
      simp only [d2047, d205594, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h8 (q : Pattern) (ha : d2048 q = 1) (hb : d205595 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d2048, d205595, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d2048, d205595, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h9 (q : Pattern) (ha : d30103 q = 1) (hb : d205595 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d30103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d30103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d205596 q = 1) (hb : d207135 q = 1) : d0 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d205596, d207135, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d205596, d207135, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
  have h11 (q : Pattern) (ha : d205597 q = 1) (hb : d207136 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d205597, d207136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d205597, d207136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h12 (q : Pattern) (ha : d205598 q = 1) (hb : d207137 q = 1) : d0 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d205598, d207137, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d205598, d207137, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  exact h12 p ha hb
theorem andIntro48529 (p : Pattern) (ha : d205605 p = 1) (hb : d207143 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d205582 q = 1) (hb : d207126 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d205582, d207126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48522 q ha hb
    | true =>
      simp only [d205582, d207126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d205583 q = 1) (hb : d207127 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d205583, d207127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d205583, d207127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d205584 q = 1) (hb : d207128 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d205584, d207128, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d205584, d207128, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d205585 q = 1) (hb : d207129 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d205585, d207129, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d205585, d207129, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d205599 q = 1) (hb : d207138 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d205599, d207138, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48528 q ha hb
    | true =>
      simp only [d205599, d207138, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d205600 q = 1) (hb : d207139 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d205600, d207139, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d205600, d207139, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d205601 q = 1) (hb : d207140 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d205601, d207140, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d205601, d207140, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d205602 q = 1) (hb : d207141 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d205602, d207141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d205602, d207141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d205603 q = 1) (hb : d207142 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d205603, d207142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d205603, d207142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d205604 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d205605 q = 1) (hb : d207143 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d205605, d207143, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d205605, d207143, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
  exact h11 p ha hb
theorem andIntro48530 (p : Pattern) (ha : d2046 p = 1) (hb : d53297 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d13 q = 1) (hb : d127 q = 1) : d0 q = 1 := by
    cases bit : q 248 with
    | false =>
      simp only [d13, d127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d13, d127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d307 q = 1) (hb : d52106 q = 1) : d0 q = 1 := by
    cases bit : q 247 with
    | false =>
      simp only [d307, d52106, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d307, d52106, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d1997 q = 1) (hb : d53276 q = 1) : d0 q = 1 := by
    cases bit : q 246 with
    | false =>
      simp only [d1997, d53276, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d1997, d53276, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d53295 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d2013 q = 1) (hb : d53296 q = 1) : d0 q = 1 := by
    cases bit : q 226 with
    | false =>
      simp only [d2013, d53296, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d2013, d53296, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d2027 q = 1) (hb : d53297 q = 1) : d0 q = 1 := by
    cases bit : q 225 with
    | false =>
      simp only [d2027, d53297, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d2027, d53297, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d0 q = 1) (hb : d53297 q = 1) : d0 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d2046 q = 1) (hb : d53297 q = 1) : d0 q = 1 := by
    cases bit : q 224 with
    | false =>
      simp only [d2046, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d2046, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro48531 (p : Pattern) (ha : d205598 p = 1) (hb : d207150 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d205578 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d53293 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d5238 q = 1) (hb : d205576 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d5238, d205576, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d5238, d205576, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48530 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d205577 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d5239 q = 1) (hb : d205578 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d5239, d205578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d5239, d205578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d205578 q = 1) (hb : d207147 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d207147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d207147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d205595 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d2047 q = 1) (hb : d205594 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d2047, d205594, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48526 q ha hb
    | true =>
      simp only [d2047, d205594, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d2048 q = 1) (hb : d205595 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d2048, d205595, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d2048, d205595, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h10 (q : Pattern) (ha : d30103 q = 1) (hb : d205595 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d30103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d30103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d205596 q = 1) (hb : d207148 q = 1) : d0 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d205596, d207148, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d205596, d207148, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
  have h12 (q : Pattern) (ha : d205597 q = 1) (hb : d207149 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d205597, d207149, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d205597, d207149, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
  have h13 (q : Pattern) (ha : d205598 q = 1) (hb : d207150 q = 1) : d0 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d205598, d207150, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d205598, d207150, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
  exact h13 p ha hb
theorem andIntro48532 (p : Pattern) (ha : d205610 p = 1) (hb : d207156 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d205599 q = 1) (hb : d207151 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d205599, d207151, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48531 q ha hb
    | true =>
      simp only [d205599, d207151, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d205600 q = 1) (hb : d207152 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d205600, d207152, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d205600, d207152, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d205601 q = 1) (hb : d207153 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d205601, d207153, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d205601, d207153, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d205602 q = 1) (hb : d207154 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d205602, d207154, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d205602, d207154, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d205609 q = 1) (hb : d207155 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d205609, d207155, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d205609, d207155, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d205610 q = 1) (hb : d207156 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d205610, d207156, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d205610, d207156, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro48533 (p : Pattern) (ha : d205610 p = 1) (hb : d207162 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d205599 q = 1) (hb : d207138 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d205599, d207138, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48528 q ha hb
    | true =>
      simp only [d205599, d207138, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d205600 q = 1) (hb : d207139 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d205600, d207139, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d205600, d207139, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d205601 q = 1) (hb : d207140 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d205601, d207140, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d205601, d207140, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d205602 q = 1) (hb : d207141 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d205602, d207141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d205602, d207141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d205609 q = 1) (hb : d207161 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d205609, d207161, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d205609, d207161, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d205610 q = 1) (hb : d207162 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d205610, d207162, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d205610, d207162, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro48534 (p : Pattern) (ha : d205617 p = 1) (hb : d207168 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d205606 q = 1) (hb : d207144 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d205606, d207144, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48523 q ha hb
    | true =>
      simp only [d205606, d207144, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48529 q ha hb
  have h2 (q : Pattern) (ha : d205607 q = 1) (hb : d207145 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d205607, d207145, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d205607, d207145, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d205608 q = 1) (hb : d207146 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d205608, d207146, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d205608, d207146, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d205611 q = 1) (hb : d207157 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d205611, d207157, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48529 q ha hb
    | true =>
      simp only [d205611, d207157, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48532 q ha hb
  have h5 (q : Pattern) (ha : d205612 q = 1) (hb : d207158 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d205612, d207158, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d205612, d207158, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d205613 q = 1) (hb : d207159 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d205613, d207159, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d205613, d207159, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d205614 q = 1) (hb : d207160 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d205614, d207160, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d205614, d207160, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d205611 q = 1) (hb : d207163 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d205611, d207163, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48529 q ha hb
    | true =>
      simp only [d205611, d207163, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48533 q ha hb
  have h9 (q : Pattern) (ha : d205612 q = 1) (hb : d207164 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d205612, d207164, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d205612, d207164, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d205613 q = 1) (hb : d207165 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d205613, d207165, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d205613, d207165, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d205615 q = 1) (hb : d207166 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d205615, d207166, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d205615, d207166, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d205616 q = 1) (hb : d207167 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d205616, d207167, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d205616, d207167, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d205617 q = 1) (hb : d207168 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d205617, d207168, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d205617, d207168, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h13 p ha hb
theorem andIntro48535 (p : Pattern) (ha : d205621 p = 1) (hb : d207172 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d205611 q = 1) (hb : d207163 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d205611, d207163, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48529 q ha hb
    | true =>
      simp only [d205611, d207163, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48533 q ha hb
  have h2 (q : Pattern) (ha : d205612 q = 1) (hb : d207164 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d205612, d207164, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d205612, d207164, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d205613 q = 1) (hb : d207165 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d205613, d207165, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d205613, d207165, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d205615 q = 1) (hb : d207166 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d205615, d207166, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d205615, d207166, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d205620 q = 1) (hb : d207171 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d205620, d207171, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d205620, d207171, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d205621 q = 1) (hb : d207172 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d205621, d207172, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d205621, d207172, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro48536 (p : Pattern) (ha : d205627 p = 1) (hb : d207178 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d205618 q = 1) (hb : d207169 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d205618, d207169, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48534 q ha hb
    | true =>
      simp only [d205618, d207169, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d205619 q = 1) (hb : d207170 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d205619, d207170, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d205619, d207170, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d205622 q = 1) (hb : d207173 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d205622, d207173, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48535 q ha hb
    | true =>
      simp only [d205622, d207173, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d205623 q = 1) (hb : d207174 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d205623, d207174, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d205623, d207174, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d205624 q = 1) (hb : d207175 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d205624, d207175, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d205624, d207175, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d205625 q = 1) (hb : d207176 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d205625, d207176, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d205625, d207176, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d205626 q = 1) (hb : d207177 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d205626, d207177, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d205626, d207177, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d205627 q = 1) (hb : d207178 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d205627, d207178, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d205627, d207178, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro48537 (p : Pattern) (ha : d205631 p = 1) (hb : d207182 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d205622 q = 1) (hb : d207173 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d205622, d207173, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48535 q ha hb
    | true =>
      simp only [d205622, d207173, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d205623 q = 1) (hb : d207174 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d205623, d207174, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d205623, d207174, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d205628 q = 1) (hb : d207179 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d205628, d207179, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d205628, d207179, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d205629 q = 1) (hb : d207180 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d205629, d207180, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d205629, d207180, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d205630 q = 1) (hb : d207181 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d205630, d207181, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d205630, d207181, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d205631 q = 1) (hb : d207182 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d205631, d207182, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d205631, d207182, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro48538 (p : Pattern) (ha : d205637 p = 1) (hb : d207188 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d205632 q = 1) (hb : d207183 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d205632, d207183, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48536 q ha hb
    | true =>
      simp only [d205632, d207183, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48537 q ha hb
  have h2 (q : Pattern) (ha : d205633 q = 1) (hb : d207184 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d205633, d207184, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d205633, d207184, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d205634 q = 1) (hb : d207185 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d205634, d207185, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d205634, d207185, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d205635 q = 1) (hb : d207186 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d205635, d207186, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d205635, d207186, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d205636 q = 1) (hb : d207187 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d205636, d207187, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d205636, d207187, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d205637 q = 1) (hb : d207188 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d205637, d207188, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d205637, d207188, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro48539 (p : Pattern) (ha : d205640 p = 1) (hb : d207191 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d205618 q = 1) (hb : d207169 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d205618, d207169, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48534 q ha hb
    | true =>
      simp only [d205618, d207169, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d205619 q = 1) (hb : d207170 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d205619, d207170, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d205619, d207170, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d205622 q = 1) (hb : d207173 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d205622, d207173, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48535 q ha hb
    | true =>
      simp only [d205622, d207173, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d205623 q = 1) (hb : d207174 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d205623, d207174, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d205623, d207174, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d205624 q = 1) (hb : d207175 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d205624, d207175, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d205624, d207175, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d205625 q = 1) (hb : d207176 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d205625, d207176, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d205625, d207176, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d205626 q = 1) (hb : d207177 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d205626, d207177, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d205626, d207177, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d205640 q = 1) (hb : d207191 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d205640, d207191, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d205640, d207191, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro48540 (p : Pattern) (ha : d205641 p = 1) (hb : d207192 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d205622 q = 1) (hb : d207173 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d205622, d207173, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48535 q ha hb
    | true =>
      simp only [d205622, d207173, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d205623 q = 1) (hb : d207174 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d205623, d207174, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d205623, d207174, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d205628 q = 1) (hb : d207179 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d205628, d207179, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d205628, d207179, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d205629 q = 1) (hb : d207180 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d205629, d207180, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d205629, d207180, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d205630 q = 1) (hb : d207181 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d205630, d207181, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d205630, d207181, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d205641 q = 1) (hb : d207192 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d205641, d207192, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d205641, d207192, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro48541 (p : Pattern) (ha : d205647 p = 1) (hb : d207198 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d205632 q = 1) (hb : d207183 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d205632, d207183, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48536 q ha hb
    | true =>
      simp only [d205632, d207183, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48537 q ha hb
  have h2 (q : Pattern) (ha : d205633 q = 1) (hb : d207184 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d205633, d207184, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d205633, d207184, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d205634 q = 1) (hb : d207185 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d205634, d207185, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d205634, d207185, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d205635 q = 1) (hb : d207186 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d205635, d207186, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d205635, d207186, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d205636 q = 1) (hb : d207187 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d205636, d207187, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d205636, d207187, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d205642 q = 1) (hb : d207193 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d205642, d207193, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48539 q ha hb
    | true =>
      simp only [d205642, d207193, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48540 q ha hb
  have h7 (q : Pattern) (ha : d205643 q = 1) (hb : d207194 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d205643, d207194, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d205643, d207194, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d205644 q = 1) (hb : d207195 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d205644, d207195, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d205644, d207195, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d205645 q = 1) (hb : d207196 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d205645, d207196, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d205645, d207196, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d205646 q = 1) (hb : d207197 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d205646, d207197, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d205646, d207197, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d205647 q = 1) (hb : d207198 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d205647, d207198, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d205647, d207198, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro48542 (p : Pattern) (ha : d205617 p = 1) (hb : d207232 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d205606 q = 1) (hb : d207144 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d205606, d207144, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48523 q ha hb
    | true =>
      simp only [d205606, d207144, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48529 q ha hb
  have h2 (q : Pattern) (ha : d205607 q = 1) (hb : d207145 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d205607, d207145, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d205607, d207145, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d205608 q = 1) (hb : d207146 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d205608, d207146, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d205608, d207146, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d205611 q = 1) (hb : d207157 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d205611, d207157, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48529 q ha hb
    | true =>
      simp only [d205611, d207157, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48532 q ha hb
  have h5 (q : Pattern) (ha : d205612 q = 1) (hb : d207158 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d205612, d207158, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d205612, d207158, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d205613 q = 1) (hb : d207159 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d205613, d207159, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d205613, d207159, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d205614 q = 1) (hb : d207160 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d205614, d207160, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d205614, d207160, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d205615 q = 1) (hb : d207230 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d205615, d207230, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d205615, d207230, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d205616 q = 1) (hb : d207231 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d205616, d207231, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d205616, d207231, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d205617 q = 1) (hb : d207232 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d205617, d207232, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d205617, d207232, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h10 p ha hb
theorem andIntro48543 (p : Pattern) (ha : d205627 p = 1) (hb : d207242 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d205618 q = 1) (hb : d207233 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d205618, d207233, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48542 q ha hb
    | true =>
      simp only [d205618, d207233, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d205619 q = 1) (hb : d207234 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d205619, d207234, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d205619, d207234, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d205622 q = 1) (hb : d207173 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d205622, d207173, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48535 q ha hb
    | true =>
      simp only [d205622, d207173, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d205623 q = 1) (hb : d207174 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d205623, d207174, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d205623, d207174, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d205624 q = 1) (hb : d207239 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d205624, d207239, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d205624, d207239, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d205625 q = 1) (hb : d207240 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d205625, d207240, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d205625, d207240, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d205626 q = 1) (hb : d207241 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d205626, d207241, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d205626, d207241, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d205627 q = 1) (hb : d207242 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d205627, d207242, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d205627, d207242, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro48544 (p : Pattern) (ha : d205652 p = 1) (hb : d207203 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d205618 q = 1) (hb : d207169 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d205618, d207169, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48534 q ha hb
    | true =>
      simp only [d205618, d207169, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d205619 q = 1) (hb : d207170 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d205619, d207170, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d205619, d207170, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d205622 q = 1) (hb : d207173 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d205622, d207173, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48535 q ha hb
    | true =>
      simp only [d205622, d207173, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d205623 q = 1) (hb : d207174 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d205623, d207174, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d205623, d207174, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d205624 q = 1) (hb : d207175 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d205624, d207175, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d205624, d207175, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d205625 q = 1) (hb : d207176 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d205625, d207176, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d205625, d207176, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d205651 q = 1) (hb : d207202 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d205651, d207202, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d205651, d207202, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d205652 q = 1) (hb : d207203 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d205652, d207203, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d205652, d207203, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro48545 (p : Pattern) (ha : d205654 p = 1) (hb : d207205 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d205622 q = 1) (hb : d207173 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d205622, d207173, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48535 q ha hb
    | true =>
      simp only [d205622, d207173, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d205623 q = 1) (hb : d207174 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d205623, d207174, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d205623, d207174, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d205628 q = 1) (hb : d207179 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d205628, d207179, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d205628, d207179, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d205629 q = 1) (hb : d207180 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d205629, d207180, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d205629, d207180, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d205653 q = 1) (hb : d207204 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d205653, d207204, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d205653, d207204, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d205654 q = 1) (hb : d207205 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d205654, d207205, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d205654, d207205, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro48546 (p : Pattern) (ha : d205661 p = 1) (hb : d207212 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d205618 q = 1) (hb : d207169 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d205618, d207169, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48534 q ha hb
    | true =>
      simp only [d205618, d207169, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d205619 q = 1) (hb : d207170 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d205619, d207170, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d205619, d207170, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d205622 q = 1) (hb : d207173 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d205622, d207173, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48535 q ha hb
    | true =>
      simp only [d205622, d207173, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d205623 q = 1) (hb : d207174 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d205623, d207174, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d205623, d207174, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d205624 q = 1) (hb : d207175 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d205624, d207175, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d205624, d207175, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d205659 q = 1) (hb : d207210 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d205659, d207210, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d205659, d207210, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d205660 q = 1) (hb : d207211 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d205660, d207211, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d205660, d207211, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d205661 q = 1) (hb : d207212 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d205661, d207212, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d205661, d207212, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro48547 (p : Pattern) (ha : d205664 p = 1) (hb : d207215 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d205622 q = 1) (hb : d207173 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d205622, d207173, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48535 q ha hb
    | true =>
      simp only [d205622, d207173, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d205623 q = 1) (hb : d207174 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d205623, d207174, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d205623, d207174, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d205628 q = 1) (hb : d207179 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d205628, d207179, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d205628, d207179, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d205662 q = 1) (hb : d207213 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d205662, d207213, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d205662, d207213, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d205663 q = 1) (hb : d207214 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d205663, d207214, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d205663, d207214, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d205664 q = 1) (hb : d207215 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d205664, d207215, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d205664, d207215, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro48548 (p : Pattern) (ha : d205679 p = 1) (hb : d207227 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d205669 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d205670 q = 1) (hb : d207219 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d205670, d207219, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d205670, d207219, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48523 q ha hb
  have h3 (q : Pattern) (ha : d205671 q = 1) (hb : d207220 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d205671, d207220, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d205671, d207220, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d205672 q = 1) (hb : d207221 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d205672, d207221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d205672, d207221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d205673 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d205674 q = 1) (hb : d207222 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d205674, d207222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48523 q ha hb
    | true =>
      simp only [d205674, d207222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d205675 q = 1) (hb : d207223 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d205675, d207223, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d205675, d207223, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d205676 q = 1) (hb : d207224 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d205676, d207224, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d205676, d207224, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d205677 q = 1) (hb : d207225 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d205677, d207225, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d205677, d207225, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d205606 q = 1) (hb : d207144 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d205606, d207144, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48523 q ha hb
    | true =>
      simp only [d205606, d207144, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48529 q ha hb
  have h11 (q : Pattern) (ha : d205607 q = 1) (hb : d207145 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d205607, d207145, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d205607, d207145, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d205608 q = 1) (hb : d207146 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d205608, d207146, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d205608, d207146, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d205611 q = 1) (hb : d207157 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d205611, d207157, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48529 q ha hb
    | true =>
      simp only [d205611, d207157, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48532 q ha hb
  have h14 (q : Pattern) (ha : d205612 q = 1) (hb : d207158 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d205612, d207158, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d205612, d207158, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d205613 q = 1) (hb : d207159 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d205613, d207159, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d205613, d207159, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d205614 q = 1) (hb : d207160 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d205614, d207160, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d205614, d207160, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d205678 q = 1) (hb : d207226 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d205678, d207226, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d205678, d207226, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d205679 q = 1) (hb : d207227 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d205679, d207227, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d205679, d207227, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h18 p ha hb
theorem andIntro48549 (p : Pattern) (ha : d205685 p = 1) (hb : d207238 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d205680 q = 1) (hb : d207228 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d205680, d207228, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48548 q ha hb
    | true =>
      simp only [d205680, d207228, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d205681 q = 1) (hb : d207229 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d205681, d207229, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d205681, d207229, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d205618 q = 1) (hb : d207233 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d205618, d207233, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48542 q ha hb
    | true =>
      simp only [d205618, d207233, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d205619 q = 1) (hb : d207234 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d205619, d207234, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d205619, d207234, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d205682 q = 1) (hb : d207235 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d205682, d207235, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d205682, d207235, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d205683 q = 1) (hb : d207236 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d205683, d207236, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d205683, d207236, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d205684 q = 1) (hb : d207237 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d205684, d207237, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d205684, d207237, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d205685 q = 1) (hb : d207238 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d205685, d207238, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d205685, d207238, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro48550 (p : Pattern) (ha : d205691 p = 1) (hb : d207248 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d205618 q = 1) (hb : d207169 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d205618, d207169, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48534 q ha hb
    | true =>
      simp only [d205618, d207169, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d205619 q = 1) (hb : d207170 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d205619, d207170, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d205619, d207170, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d205688 q = 1) (hb : d207245 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d205688, d207245, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d205688, d207245, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d205689 q = 1) (hb : d207246 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d205689, d207246, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d205689, d207246, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d205690 q = 1) (hb : d207247 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d205690, d207247, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d205690, d207247, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d205691 q = 1) (hb : d207248 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d205691, d207248, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d205691, d207248, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro48551 (p : Pattern) (ha : d205697 p = 1) (hb : d207254 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d205655 q = 1) (hb : d207206 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d205655, d207206, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48544 q ha hb
    | true =>
      simp only [d205655, d207206, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48545 q ha hb
  have h2 (q : Pattern) (ha : d205656 q = 1) (hb : d207207 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d205656, d207207, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d205656, d207207, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d205657 q = 1) (hb : d207208 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d205657, d207208, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d205657, d207208, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d205658 q = 1) (hb : d207209 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d205658, d207209, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d205658, d207209, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d205665 q = 1) (hb : d207216 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d205665, d207216, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48546 q ha hb
    | true =>
      simp only [d205665, d207216, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48547 q ha hb
  have h6 (q : Pattern) (ha : d205666 q = 1) (hb : d207217 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d205666, d207217, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d205666, d207217, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d205667 q = 1) (hb : d207218 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d205667, d207218, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d205667, d207218, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d205686 q = 1) (hb : d207243 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d205686, d207243, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48549 q ha hb
    | true =>
      simp only [d205686, d207243, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48543 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d205632 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d205687 q = 1) (hb : d207244 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d205687, d207244, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d205687, d207244, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
  have h11 (q : Pattern) (ha : d205692 q = 1) (hb : d207249 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d205692, d207249, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48550 q ha hb
    | true =>
      simp only [d205692, d207249, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d205693 q = 1) (hb : d207250 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d205693, d207250, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d205693, d207250, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d205694 q = 1) (hb : d207251 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d205694, d207251, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d205694, d207251, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d205695 q = 1) (hb : d207252 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d205695, d207252, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d205695, d207252, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d205696 q = 1) (hb : d207253 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d205696, d207253, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d205696, d207253, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d205697 q = 1) (hb : d207254 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d205697, d207254, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d205697, d207254, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  exact h16 p ha hb
theorem andIntro48552 (p : Pattern) (ha : d205640 p = 1) (hb : d207267 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d205618 q = 1) (hb : d207233 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d205618, d207233, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48542 q ha hb
    | true =>
      simp only [d205618, d207233, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d205619 q = 1) (hb : d207234 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d205619, d207234, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d205619, d207234, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d205622 q = 1) (hb : d207173 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d205622, d207173, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48535 q ha hb
    | true =>
      simp only [d205622, d207173, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d205623 q = 1) (hb : d207174 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d205623, d207174, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d205623, d207174, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d205624 q = 1) (hb : d207239 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d205624, d207239, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d205624, d207239, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d205625 q = 1) (hb : d207240 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d205625, d207240, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d205625, d207240, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d205626 q = 1) (hb : d207241 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d205626, d207241, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d205626, d207241, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d205640 q = 1) (hb : d207267 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d205640, d207267, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d205640, d207267, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro48553 (p : Pattern) (ha : d205698 p = 1) (hb : d207255 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d205618 q = 1) (hb : d207169 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d205618, d207169, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48534 q ha hb
    | true =>
      simp only [d205618, d207169, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d205619 q = 1) (hb : d207170 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d205619, d207170, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d205619, d207170, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d205622 q = 1) (hb : d207173 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d205622, d207173, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48535 q ha hb
    | true =>
      simp only [d205622, d207173, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d205623 q = 1) (hb : d207174 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d205623, d207174, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d205623, d207174, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d205624 q = 1) (hb : d207175 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d205624, d207175, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d205624, d207175, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d205625 q = 1) (hb : d207176 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d205625, d207176, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d205625, d207176, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d205651 q = 1) (hb : d207202 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d205651, d207202, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d205651, d207202, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d205698 q = 1) (hb : d207255 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d205698, d207255, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d205698, d207255, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro48554 (p : Pattern) (ha : d205699 p = 1) (hb : d207256 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d205622 q = 1) (hb : d207173 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d205622, d207173, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48535 q ha hb
    | true =>
      simp only [d205622, d207173, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d205623 q = 1) (hb : d207174 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d205623, d207174, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d205623, d207174, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d205628 q = 1) (hb : d207179 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d205628, d207179, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d205628, d207179, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d205629 q = 1) (hb : d207180 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d205629, d207180, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d205629, d207180, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d205653 q = 1) (hb : d207204 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d205653, d207204, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d205653, d207204, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d205699 q = 1) (hb : d207256 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d205699, d207256, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d205699, d207256, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro48555 (p : Pattern) (ha : d205704 p = 1) (hb : d207261 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d205618 q = 1) (hb : d207169 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d205618, d207169, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48534 q ha hb
    | true =>
      simp only [d205618, d207169, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d205619 q = 1) (hb : d207170 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d205619, d207170, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d205619, d207170, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d205622 q = 1) (hb : d207173 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d205622, d207173, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48535 q ha hb
    | true =>
      simp only [d205622, d207173, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d205623 q = 1) (hb : d207174 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d205623, d207174, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d205623, d207174, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d205624 q = 1) (hb : d207175 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d205624, d207175, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d205624, d207175, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d205659 q = 1) (hb : d207210 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d205659, d207210, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d205659, d207210, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d205660 q = 1) (hb : d207211 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d205660, d207211, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d205660, d207211, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d205704 q = 1) (hb : d207261 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d205704, d207261, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d205704, d207261, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro48556 (p : Pattern) (ha : d205705 p = 1) (hb : d207262 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d205622 q = 1) (hb : d207173 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d205622, d207173, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48535 q ha hb
    | true =>
      simp only [d205622, d207173, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d205623 q = 1) (hb : d207174 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d205623, d207174, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d205623, d207174, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d205628 q = 1) (hb : d207179 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d205628, d207179, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d205628, d207179, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d205662 q = 1) (hb : d207213 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d205662, d207213, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d205662, d207213, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d205663 q = 1) (hb : d207214 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d205663, d207214, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d205663, d207214, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d205705 q = 1) (hb : d207262 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d205705, d207262, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d205705, d207262, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro48557 (p : Pattern) (ha : d205709 p = 1) (hb : d207266 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d205680 q = 1) (hb : d207228 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d205680, d207228, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48548 q ha hb
    | true =>
      simp only [d205680, d207228, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d205681 q = 1) (hb : d207229 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d205681, d207229, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d205681, d207229, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d205618 q = 1) (hb : d207233 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d205618, d207233, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48542 q ha hb
    | true =>
      simp only [d205618, d207233, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d205619 q = 1) (hb : d207234 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d205619, d207234, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d205619, d207234, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d205682 q = 1) (hb : d207235 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d205682, d207235, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d205682, d207235, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d205683 q = 1) (hb : d207236 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d205683, d207236, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d205683, d207236, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d205684 q = 1) (hb : d207237 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d205684, d207237, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d205684, d207237, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d205709 q = 1) (hb : d207266 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d205709, d207266, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d205709, d207266, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro48558 (p : Pattern) (ha : d205712 p = 1) (hb : d207270 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d205618 q = 1) (hb : d207169 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d205618, d207169, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48534 q ha hb
    | true =>
      simp only [d205618, d207169, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d205619 q = 1) (hb : d207170 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d205619, d207170, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d205619, d207170, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d205688 q = 1) (hb : d207245 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d205688, d207245, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d205688, d207245, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d205689 q = 1) (hb : d207246 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d205689, d207246, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d205689, d207246, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d205690 q = 1) (hb : d207247 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d205690, d207247, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d205690, d207247, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d205712 q = 1) (hb : d207270 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d205712, d207270, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d205712, d207270, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro48559 (p : Pattern) (ha : d205718 p = 1) (hb : d207276 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d205655 q = 1) (hb : d207206 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d205655, d207206, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48544 q ha hb
    | true =>
      simp only [d205655, d207206, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48545 q ha hb
  have h2 (q : Pattern) (ha : d205656 q = 1) (hb : d207207 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d205656, d207207, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d205656, d207207, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d205657 q = 1) (hb : d207208 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d205657, d207208, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d205657, d207208, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d205658 q = 1) (hb : d207209 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d205658, d207209, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d205658, d207209, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d205665 q = 1) (hb : d207216 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d205665, d207216, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48546 q ha hb
    | true =>
      simp only [d205665, d207216, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48547 q ha hb
  have h6 (q : Pattern) (ha : d205666 q = 1) (hb : d207217 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d205666, d207217, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d205666, d207217, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d205667 q = 1) (hb : d207218 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d205667, d207218, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d205667, d207218, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d205686 q = 1) (hb : d207243 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d205686, d207243, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48549 q ha hb
    | true =>
      simp only [d205686, d207243, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48543 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d205632 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d205687 q = 1) (hb : d207244 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d205687, d207244, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d205687, d207244, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
  have h11 (q : Pattern) (ha : d205692 q = 1) (hb : d207249 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d205692, d207249, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48550 q ha hb
    | true =>
      simp only [d205692, d207249, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d205693 q = 1) (hb : d207250 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d205693, d207250, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d205693, d207250, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d205694 q = 1) (hb : d207251 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d205694, d207251, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d205694, d207251, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d205695 q = 1) (hb : d207252 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d205695, d207252, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d205695, d207252, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d205696 q = 1) (hb : d207253 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d205696, d207253, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d205696, d207253, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d205700 q = 1) (hb : d207257 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d205700, d207257, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48553 q ha hb
    | true =>
      simp only [d205700, d207257, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48554 q ha hb
  have h17 (q : Pattern) (ha : d205701 q = 1) (hb : d207258 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d205701, d207258, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d205701, d207258, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d205702 q = 1) (hb : d207259 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d205702, d207259, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d205702, d207259, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h19 (q : Pattern) (ha : d205703 q = 1) (hb : d207260 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d205703, d207260, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d205703, d207260, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d205706 q = 1) (hb : d207263 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d205706, d207263, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48555 q ha hb
    | true =>
      simp only [d205706, d207263, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48556 q ha hb
  have h21 (q : Pattern) (ha : d205707 q = 1) (hb : d207264 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d205707, d207264, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d205707, d207264, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
  have h22 (q : Pattern) (ha : d205708 q = 1) (hb : d207265 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d205708, d207265, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d205708, d207265, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h23 (q : Pattern) (ha : d205710 q = 1) (hb : d207268 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d205710, d207268, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48557 q ha hb
    | true =>
      simp only [d205710, d207268, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48552 q ha hb
  have h24 (q : Pattern) (ha : d0 q = 1) (hb : d205642 q = 1) : d0 q = 1 := by
    exact ha
  have h25 (q : Pattern) (ha : d205711 q = 1) (hb : d207269 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d205711, d207269, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
    | true =>
      simp only [d205711, d207269, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q hb ha
  have h26 (q : Pattern) (ha : d205713 q = 1) (hb : d207271 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d205713, d207271, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48558 q ha hb
    | true =>
      simp only [d205713, d207271, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h27 (q : Pattern) (ha : d205714 q = 1) (hb : d207272 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d205714, d207272, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h26 q ha hb
    | true =>
      simp only [d205714, d207272, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h28 (q : Pattern) (ha : d205715 q = 1) (hb : d207273 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d205715, d207273, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q ha hb
    | true =>
      simp only [d205715, d207273, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h27 q ha hb
  have h29 (q : Pattern) (ha : d205716 q = 1) (hb : d207274 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d205716, d207274, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
    | true =>
      simp only [d205716, d207274, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h28 q ha hb
  have h30 (q : Pattern) (ha : d205717 q = 1) (hb : d207275 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d205717, d207275, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d205717, d207275, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h29 q ha hb
  have h31 (q : Pattern) (ha : d205718 q = 1) (hb : d207276 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d205718, d207276, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d205718, d207276, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h30 q ha hb
  exact h31 p ha hb
theorem andIntro48560 (p : Pattern) (ha : d205725 p = 1) (hb : d207288 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d205632 q = 1) (hb : d207278 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d205632, d207278, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48543 q ha hb
    | true =>
      simp only [d205632, d207278, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48537 q ha hb
  have h2 (q : Pattern) (ha : d205633 q = 1) (hb : d207279 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d205633, d207279, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d205633, d207279, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d205634 q = 1) (hb : d207280 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d205634, d207280, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d205634, d207280, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d205635 q = 1) (hb : d207281 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d205635, d207281, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d205635, d207281, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d205636 q = 1) (hb : d207282 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d205636, d207282, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d205636, d207282, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d205720 q = 1) (hb : d207283 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d205720, d207283, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48537 q ha hb
    | true =>
      simp only [d205720, d207283, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d205721 q = 1) (hb : d207284 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d205721, d207284, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d205721, d207284, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d205722 q = 1) (hb : d207285 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d205722, d207285, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d205722, d207285, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d205723 q = 1) (hb : d207286 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d205723, d207286, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d205723, d207286, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d205724 q = 1) (hb : d207287 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d205724, d207287, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d205724, d207287, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d205725 q = 1) (hb : d207288 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d205725, d207288, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d205725, d207288, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro48561 (p : Pattern) (ha : d205731 p = 1) (hb : d207294 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d205720 q = 1) (hb : d207283 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d205720, d207283, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48537 q ha hb
    | true =>
      simp only [d205720, d207283, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d205721 q = 1) (hb : d207284 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d205721, d207284, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d205721, d207284, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d205722 q = 1) (hb : d207285 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d205722, d207285, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d205722, d207285, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d205723 q = 1) (hb : d207286 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d205723, d207286, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d205723, d207286, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d205724 q = 1) (hb : d207287 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d205724, d207287, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d205724, d207287, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d205726 q = 1) (hb : d207289 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d205726, d207289, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48540 q ha hb
    | true =>
      simp only [d205726, d207289, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d205727 q = 1) (hb : d207290 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d205727, d207290, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d205727, d207290, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d205728 q = 1) (hb : d207291 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d205728, d207291, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d205728, d207291, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d205729 q = 1) (hb : d207292 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d205729, d207292, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d205729, d207292, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d205730 q = 1) (hb : d207293 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d205730, d207293, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d205730, d207293, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d205731 q = 1) (hb : d207294 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d205731, d207294, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d205731, d207294, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro48562 (p : Pattern) (ha : d205738 p = 1) (hb : d207301 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d205710 q = 1) (hb : d207268 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d205710, d207268, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48557 q ha hb
    | true =>
      simp only [d205710, d207268, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48552 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d205642 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d205711 q = 1) (hb : d207269 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d205711, d207269, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d205711, d207269, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d205713 q = 1) (hb : d207271 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d205713, d207271, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48558 q ha hb
    | true =>
      simp only [d205713, d207271, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d205714 q = 1) (hb : d207272 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d205714, d207272, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d205714, d207272, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d205715 q = 1) (hb : d207273 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d205715, d207273, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d205715, d207273, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d205736 q = 1) (hb : d207299 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d205736, d207299, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d205736, d207299, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d205737 q = 1) (hb : d207300 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d205737, d207300, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d205737, d207300, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d205738 q = 1) (hb : d207301 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d205738, d207301, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d205738, d207301, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro48563 (p : Pattern) (ha : d205740 p = 1) (hb : d207303 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d205726 q = 1) (hb : d207289 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d205726, d207289, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48540 q ha hb
    | true =>
      simp only [d205726, d207289, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d205727 q = 1) (hb : d207290 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d205727, d207290, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d205727, d207290, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d205728 q = 1) (hb : d207291 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d205728, d207291, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d205728, d207291, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d205729 q = 1) (hb : d207292 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d205729, d207292, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d205729, d207292, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d205730 q = 1) (hb : d207293 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d205730, d207293, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d205730, d207293, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d205740 q = 1) (hb : d207303 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d205740, d207303, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d205740, d207303, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro48564 (p : Pattern) (ha : d205762 p = 1) (hb : d207314 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d205749 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d205751 q = 1) (hb : d207309 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d205751, d207309, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d205751, d207309, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48522 q ha hb
  have h3 (q : Pattern) (ha : d205582 q = 1) (hb : d207126 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d205582, d207126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48522 q ha hb
    | true =>
      simp only [d205582, d207126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h4 (q : Pattern) (ha : d205752 q = 1) (hb : d207310 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d205752, d207310, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d205752, d207310, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d205583 q = 1) (hb : d207127 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d205583, d207127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d205583, d207127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h6 (q : Pattern) (ha : d205753 q = 1) (hb : d207311 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d205753, d207311, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d205753, d207311, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d205754 q = 1) (hb : d207312 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d205754, d207312, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d205754, d207312, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h8 (q : Pattern) (ha : d205755 q = 1) (hb : d207313 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d205755, d207313, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d205755, d207313, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d205761 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d205762 q = 1) (hb : d207314 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d205762, d207314, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d205762, d207314, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
  exact h10 p ha hb
theorem andIntro48565 (p : Pattern) (ha : d205777 p = 1) (hb : d207327 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d205751 q = 1) (hb : d207309 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d205751, d207309, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d205751, d207309, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48522 q ha hb
  have h2 (q : Pattern) (ha : d205582 q = 1) (hb : d207126 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d205582, d207126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48522 q ha hb
    | true =>
      simp only [d205582, d207126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d205752 q = 1) (hb : d207310 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d205752, d207310, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d205752, d207310, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d205583 q = 1) (hb : d207127 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d205583, d207127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d205583, d207127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d205753 q = 1) (hb : d207311 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d205753, d207311, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d205753, d207311, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d205754 q = 1) (hb : d207312 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d205754, d207312, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d205754, d207312, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d205772 q = 1) (hb : d207322 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d205772, d207322, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d205772, d207322, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48528 q ha hb
  have h8 (q : Pattern) (ha : d205599 q = 1) (hb : d207138 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d205599, d207138, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48528 q ha hb
    | true =>
      simp only [d205599, d207138, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d205773 q = 1) (hb : d207323 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d205773, d207323, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d205773, d207323, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d205600 q = 1) (hb : d207139 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d205600, d207139, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d205600, d207139, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h11 (q : Pattern) (ha : d205774 q = 1) (hb : d207324 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d205774, d207324, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d205774, d207324, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d205775 q = 1) (hb : d207325 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d205775, d207325, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d205775, d207325, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d205776 q = 1) (hb : d207326 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d205776, d207326, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d205776, d207326, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d205766 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d205777 q = 1) (hb : d207327 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d205777, d207327, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d205777, d207327, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  exact h15 p ha hb
theorem andIntro48566 (p : Pattern) (ha : d205782 p = 1) (hb : d207336 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d205772 q = 1) (hb : d207331 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d205772, d207331, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d205772, d207331, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48531 q ha hb
  have h2 (q : Pattern) (ha : d205599 q = 1) (hb : d207151 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d205599, d207151, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48531 q ha hb
    | true =>
      simp only [d205599, d207151, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d205773 q = 1) (hb : d207332 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d205773, d207332, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d205773, d207332, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d205600 q = 1) (hb : d207152 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d205600, d207152, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d205600, d207152, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d205774 q = 1) (hb : d207333 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d205774, d207333, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d205774, d207333, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d205775 q = 1) (hb : d207334 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d205775, d207334, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d205775, d207334, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d205781 q = 1) (hb : d207335 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d205781, d207335, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d205781, d207335, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d205782 q = 1) (hb : d207336 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d205782, d207336, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d205782, d207336, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro48567 (p : Pattern) (ha : d205788 p = 1) (hb : d207342 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d205756 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d205763 q = 1) (hb : d207315 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d205763, d207315, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d205763, d207315, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48564 q ha hb
  have h3 (q : Pattern) (ha : d205764 q = 1) (hb : d207316 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d205764, d207316, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d205764, d207316, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d205765 q = 1) (hb : d207317 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d205765, d207317, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d205765, d207317, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d205767 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d205768 q = 1) (hb : d207318 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d205768, d207318, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48564 q ha hb
    | true =>
      simp only [d205768, d207318, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d205769 q = 1) (hb : d207319 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d205769, d207319, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d205769, d207319, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d205770 q = 1) (hb : d207320 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d205770, d207320, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d205770, d207320, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d205771 q = 1) (hb : d207321 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d205771, d207321, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d205771, d207321, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d205778 q = 1) (hb : d207328 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d205778, d207328, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48564 q ha hb
    | true =>
      simp only [d205778, d207328, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48565 q ha hb
  have h11 (q : Pattern) (ha : d205779 q = 1) (hb : d207329 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d205779, d207329, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d205779, d207329, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d205780 q = 1) (hb : d207330 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d205780, d207330, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d205780, d207330, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d205783 q = 1) (hb : d207337 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d205783, d207337, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48565 q ha hb
    | true =>
      simp only [d205783, d207337, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48566 q ha hb
  have h14 (q : Pattern) (ha : d205784 q = 1) (hb : d207338 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d205784, d207338, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d205784, d207338, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d205785 q = 1) (hb : d207339 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d205785, d207339, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d205785, d207339, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d205786 q = 1) (hb : d207340 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d205786, d207340, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d205786, d207340, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d205787 q = 1) (hb : d207341 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d205787, d207341, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d205787, d207341, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d205788 q = 1) (hb : d207342 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d205788, d207342, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d205788, d207342, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h18 p ha hb
theorem andIntro48568 (p : Pattern) (ha : d205793 p = 1) (hb : d207347 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d205778 q = 1) (hb : d207328 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d205778, d207328, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48564 q ha hb
    | true =>
      simp only [d205778, d207328, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48565 q ha hb
  have h2 (q : Pattern) (ha : d205779 q = 1) (hb : d207329 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d205779, d207329, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d205779, d207329, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d205780 q = 1) (hb : d207330 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d205780, d207330, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d205780, d207330, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d205783 q = 1) (hb : d207337 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d205783, d207337, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48565 q ha hb
    | true =>
      simp only [d205783, d207337, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48566 q ha hb
  have h5 (q : Pattern) (ha : d205784 q = 1) (hb : d207338 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d205784, d207338, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d205784, d207338, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d205785 q = 1) (hb : d207339 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d205785, d207339, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d205785, d207339, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d205786 q = 1) (hb : d207340 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d205786, d207340, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d205786, d207340, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d205791 q = 1) (hb : d207345 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d205791, d207345, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d205791, d207345, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d205792 q = 1) (hb : d207346 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d205792, d207346, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d205792, d207346, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d205793 q = 1) (hb : d207347 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d205793, d207347, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d205793, d207347, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h10 p ha hb
theorem andIntro48569 (p : Pattern) (ha : d205799 p = 1) (hb : d207353 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d205789 q = 1) (hb : d207343 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d205789, d207343, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48567 q ha hb
    | true =>
      simp only [d205789, d207343, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d205790 q = 1) (hb : d207344 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d205790, d207344, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d205790, d207344, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d205794 q = 1) (hb : d207348 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d205794, d207348, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48568 q ha hb
    | true =>
      simp only [d205794, d207348, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d205795 q = 1) (hb : d207349 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d205795, d207349, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d205795, d207349, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d205796 q = 1) (hb : d207350 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d205796, d207350, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d205796, d207350, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d205797 q = 1) (hb : d207351 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d205797, d207351, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d205797, d207351, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d205798 q = 1) (hb : d207352 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d205798, d207352, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d205798, d207352, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d205799 q = 1) (hb : d207353 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d205799, d207353, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d205799, d207353, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro48570 (p : Pattern) (ha : d205782 p = 1) (hb : d207355 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d205772 q = 1) (hb : d207322 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d205772, d207322, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d205772, d207322, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48528 q ha hb
  have h2 (q : Pattern) (ha : d205599 q = 1) (hb : d207138 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d205599, d207138, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48528 q ha hb
    | true =>
      simp only [d205599, d207138, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d205773 q = 1) (hb : d207323 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d205773, d207323, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d205773, d207323, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d205600 q = 1) (hb : d207139 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d205600, d207139, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d205600, d207139, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d205774 q = 1) (hb : d207324 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d205774, d207324, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d205774, d207324, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d205775 q = 1) (hb : d207325 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d205775, d207325, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d205775, d207325, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d205781 q = 1) (hb : d207354 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d205781, d207354, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d205781, d207354, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d205782 q = 1) (hb : d207355 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d205782, d207355, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d205782, d207355, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro48571 (p : Pattern) (ha : d205801 p = 1) (hb : d207361 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d205783 q = 1) (hb : d207356 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d205783, d207356, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48565 q ha hb
    | true =>
      simp only [d205783, d207356, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48570 q ha hb
  have h2 (q : Pattern) (ha : d205784 q = 1) (hb : d207357 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d205784, d207357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d205784, d207357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d205785 q = 1) (hb : d207358 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d205785, d207358, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d205785, d207358, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d205791 q = 1) (hb : d207359 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d205791, d207359, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d205791, d207359, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d205800 q = 1) (hb : d207360 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d205800, d207360, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d205800, d207360, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d205801 q = 1) (hb : d207361 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d205801, d207361, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d205801, d207361, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro48572 (p : Pattern) (ha : d205807 p = 1) (hb : d207367 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d205794 q = 1) (hb : d207348 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d205794, d207348, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48568 q ha hb
    | true =>
      simp only [d205794, d207348, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d205795 q = 1) (hb : d207349 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d205795, d207349, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d205795, d207349, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d205802 q = 1) (hb : d207362 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d205802, d207362, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48571 q ha hb
    | true =>
      simp only [d205802, d207362, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d205803 q = 1) (hb : d207363 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d205803, d207363, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d205803, d207363, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d205804 q = 1) (hb : d207364 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d205804, d207364, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d205804, d207364, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d205805 q = 1) (hb : d207365 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d205805, d207365, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d205805, d207365, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d205806 q = 1) (hb : d207366 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d205806, d207366, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d205806, d207366, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d205807 q = 1) (hb : d207367 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d205807, d207367, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d205807, d207367, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro48573 (p : Pattern) (ha : d205793 p = 1) (hb : d207371 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d205778 q = 1) (hb : d207328 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d205778, d207328, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48564 q ha hb
    | true =>
      simp only [d205778, d207328, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48565 q ha hb
  have h2 (q : Pattern) (ha : d205779 q = 1) (hb : d207329 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d205779, d207329, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d205779, d207329, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d205780 q = 1) (hb : d207330 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d205780, d207330, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d205780, d207330, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d205783 q = 1) (hb : d207337 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d205783, d207337, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48565 q ha hb
    | true =>
      simp only [d205783, d207337, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48566 q ha hb
  have h5 (q : Pattern) (ha : d205784 q = 1) (hb : d207338 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d205784, d207338, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d205784, d207338, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d205785 q = 1) (hb : d207339 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d205785, d207339, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d205785, d207339, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d205786 q = 1) (hb : d207340 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d205786, d207340, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d205786, d207340, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d205783 q = 1) (hb : d207356 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d205783, d207356, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48565 q ha hb
    | true =>
      simp only [d205783, d207356, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48570 q ha hb
  have h9 (q : Pattern) (ha : d205784 q = 1) (hb : d207357 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d205784, d207357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d205784, d207357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d205785 q = 1) (hb : d207358 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d205785, d207358, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d205785, d207358, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d205791 q = 1) (hb : d207359 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d205791, d207359, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d205791, d207359, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d205792 q = 1) (hb : d207370 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d205792, d207370, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d205792, d207370, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d205793 q = 1) (hb : d207371 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d205793, d207371, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d205793, d207371, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h13 p ha hb
theorem andIntro48574 (p : Pattern) (ha : d205818 p = 1) (hb : d207377 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d205794 q = 1) (hb : d207372 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d205794, d207372, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48573 q ha hb
    | true =>
      simp only [d205794, d207372, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d205795 q = 1) (hb : d207373 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d205795, d207373, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d205795, d207373, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d205815 q = 1) (hb : d207374 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d205815, d207374, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d205815, d207374, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d205816 q = 1) (hb : d207375 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d205816, d207375, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d205816, d207375, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d205817 q = 1) (hb : d207376 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d205817, d207376, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d205817, d207376, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d205818 q = 1) (hb : d207377 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d205818, d207377, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d205818, d207377, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro48575 (p : Pattern) (ha : d205824 p = 1) (hb : d207383 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d205808 q = 1) (hb : d207368 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d205808, d207368, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48569 q ha hb
    | true =>
      simp only [d205808, d207368, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48572 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d205813 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d205814 q = 1) (hb : d207369 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d205814, d207369, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d205814, d207369, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d205819 q = 1) (hb : d207378 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d205819, d207378, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48574 q ha hb
    | true =>
      simp only [d205819, d207378, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d205820 q = 1) (hb : d207379 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d205820, d207379, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d205820, d207379, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d205821 q = 1) (hb : d207380 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d205821, d207380, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d205821, d207380, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d205822 q = 1) (hb : d207381 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d205822, d207381, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d205822, d207381, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d205823 q = 1) (hb : d207382 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d205823, d207382, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d205823, d207382, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d205824 q = 1) (hb : d207383 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d205824, d207383, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d205824, d207383, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro48576 (p : Pattern) (ha : d205812 p = 1) (hb : d207388 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d205802 q = 1) (hb : d207362 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d205802, d207362, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48571 q ha hb
    | true =>
      simp only [d205802, d207362, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d205803 q = 1) (hb : d207363 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d205803, d207363, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d205803, d207363, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d205809 q = 1) (hb : d207385 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d205809, d207385, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d205809, d207385, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d205810 q = 1) (hb : d207386 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d205810, d207386, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d205810, d207386, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d205811 q = 1) (hb : d207387 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d205811, d207387, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d205811, d207387, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d205812 q = 1) (hb : d207388 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d205812, d207388, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d205812, d207388, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro48577 (p : Pattern) (ha : d205831 p = 1) (hb : d207394 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d205826 q = 1) (hb : d207389 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d205826, d207389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48576 q ha hb
    | true =>
      simp only [d205826, d207389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d205827 q = 1) (hb : d207390 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d205827, d207390, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d205827, d207390, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d205828 q = 1) (hb : d207391 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d205828, d207391, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d205828, d207391, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d205829 q = 1) (hb : d207392 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d205829, d207392, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d205829, d207392, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d205830 q = 1) (hb : d207393 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d205830, d207393, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d205830, d207393, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d205831 q = 1) (hb : d207394 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d205831, d207394, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d205831, d207394, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro48578 (p : Pattern) (ha : d205837 p = 1) (hb : d207400 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d205638 q = 1) (hb : d207189 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d205638, d207189, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d205638, d207189, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48538 q ha hb
  have h2 (q : Pattern) (ha : d205639 q = 1) (hb : d207190 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d205639, d207190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d205639, d207190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d205648 q = 1) (hb : d207199 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d205648, d207199, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48538 q ha hb
    | true =>
      simp only [d205648, d207199, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48541 q ha hb
  have h4 (q : Pattern) (ha : d205649 q = 1) (hb : d207200 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d205649, d207200, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d205649, d207200, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d205650 q = 1) (hb : d207201 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d205650, d207201, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d205650, d207201, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d205719 q = 1) (hb : d207277 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d205719, d207277, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48551 q ha hb
    | true =>
      simp only [d205719, d207277, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48559 q ha hb
  have h7 (q : Pattern) (ha : d205732 q = 1) (hb : d207295 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d205732, d207295, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48560 q ha hb
    | true =>
      simp only [d205732, d207295, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48561 q ha hb
  have h8 (q : Pattern) (ha : d205733 q = 1) (hb : d207296 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d205733, d207296, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d205733, d207296, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d205734 q = 1) (hb : d207297 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d205734, d207297, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d205734, d207297, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h10 (q : Pattern) (ha : d205735 q = 1) (hb : d207298 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d205735, d207298, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d205735, d207298, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d205739 q = 1) (hb : d207302 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d205739, d207302, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d205739, d207302, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48562 q ha hb
  have h12 (q : Pattern) (ha : d205741 q = 1) (hb : d207304 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d205741, d207304, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d205741, d207304, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48563 q ha hb
  have h13 (q : Pattern) (ha : d205742 q = 1) (hb : d207305 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d205742, d207305, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d205742, d207305, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d205743 q = 1) (hb : d207306 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d205743, d207306, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d205743, d207306, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h15 (q : Pattern) (ha : d205744 q = 1) (hb : d207307 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d205744, d207307, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d205744, d207307, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h16 (q : Pattern) (ha : d205745 q = 1) (hb : d207308 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d205745, d207308, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d205745, d207308, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d205825 q = 1) (hb : d207384 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d205825, d207384, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d205825, d207384, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48575 q ha hb
  have h18 (q : Pattern) (ha : d205832 q = 1) (hb : d207395 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d205832, d207395, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d205832, d207395, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48577 q ha hb
  have h19 (q : Pattern) (ha : d205833 q = 1) (hb : d207396 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d205833, d207396, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d205833, d207396, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d205834 q = 1) (hb : d207397 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d205834, d207397, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d205834, d207397, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h21 (q : Pattern) (ha : d205835 q = 1) (hb : d207398 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d205835, d207398, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d205835, d207398, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h22 (q : Pattern) (ha : d205836 q = 1) (hb : d207399 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d205836, d207399, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d205836, d207399, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h23 (q : Pattern) (ha : d205837 q = 1) (hb : d207400 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d205837, d207400, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d205837, d207400, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
  exact h23 p ha hb
theorem andIntro48579 (p : Pattern) (ha : d205843 p = 1) (hb : d207406 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d205838 q = 1) (hb : d207401 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d205838, d207401, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d205838, d207401, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48578 q ha hb
  have h2 (q : Pattern) (ha : d205839 q = 1) (hb : d207402 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d205839, d207402, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d205839, d207402, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d205840 q = 1) (hb : d207403 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d205840, d207403, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d205840, d207403, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d205841 q = 1) (hb : d207404 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d205841, d207404, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d205841, d207404, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d205842 q = 1) (hb : d207405 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d205842, d207405, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d205842, d207405, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d205843 q = 1) (hb : d207406 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d205843, d207406, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d205843, d207406, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro48580 (p : Pattern) (ha : d205849 p = 1) (hb : d207412 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d204726 q = 1) (hb : d206253 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d204726, d206253, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48309 q ha hb
    | true =>
      simp only [d204726, d206253, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48338 q ha hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d204953 q = 1) (hb : d206481 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d204953, d206481, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d204953, d206481, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48385 q ha hb
  have h3 (q : Pattern) (ha : d204954 q = 1) (hb : d206482 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d204954, d206482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d204954, d206482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d205257 q = 1) (hb : d206806 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d205257, d206806, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d205257, d206806, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48450 q ha hb
  have h5 (q : Pattern) (ha : d205258 q = 1) (hb : d206807 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d205258, d206807, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d205258, d206807, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d205259 q = 1) (hb : d206808 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d205259, d206808, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d205259, d206808, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d205562 q = 1) (hb : d207118 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d205562, d207118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d205562, d207118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48518 q ha hb
  have h8 (q : Pattern) (ha : d205563 q = 1) (hb : d207119 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d205563, d207119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d205563, d207119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d205564 q = 1) (hb : d207120 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d205564, d207120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d205564, d207120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d205565 q = 1) (hb : d207121 q = 1) : d0 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d205565, d207121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d205565, d207121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d205844 q = 1) (hb : d207407 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d205844, d207407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d205844, d207407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48579 q ha hb
  have h12 (q : Pattern) (ha : d205845 q = 1) (hb : d207408 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d205845, d207408, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d205845, d207408, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d205846 q = 1) (hb : d207409 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d205846, d207409, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d205846, d207409, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d205847 q = 1) (hb : d207410 q = 1) : d0 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d205847, d207410, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d205847, d207410, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d205848 q = 1) (hb : d207411 q = 1) : d0 q = 1 := by
    cases bit : q 10250 with
    | false =>
      simp only [d205848, d207411, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d205848, d207411, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d205849 q = 1) (hb : d207412 q = 1) : d0 q = 1 := by
    cases bit : q 260 with
    | false =>
      simp only [d205849, d207412, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d205849, d207412, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  exact h16 p ha hb
theorem andIntro48581 (p : Pattern) (ha : d205855 p = 1) (hb : d207418 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d205850 q = 1) (hb : d207413 q = 1) : d0 q = 1 := by
    cases bit : q 259 with
    | false =>
      simp only [d205850, d207413, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48580 q ha hb
    | true =>
      simp only [d205850, d207413, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d205851 q = 1) (hb : d207414 q = 1) : d0 q = 1 := by
    cases bit : q 258 with
    | false =>
      simp only [d205851, d207414, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d205851, d207414, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d205852 q = 1) (hb : d207415 q = 1) : d0 q = 1 := by
    cases bit : q 257 with
    | false =>
      simp only [d205852, d207415, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d205852, d207415, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d205853 q = 1) (hb : d207416 q = 1) : d0 q = 1 := by
    cases bit : q 256 with
    | false =>
      simp only [d205853, d207416, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d205853, d207416, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d205854 q = 1) (hb : d207417 q = 1) : d0 q = 1 := by
    cases bit : q 255 with
    | false =>
      simp only [d205854, d207417, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d205854, d207417, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d205855 q = 1) (hb : d207418 q = 1) : d0 q = 1 := by
    cases bit : q 254 with
    | false =>
      simp only [d205855, d207418, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d205855, d207418, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro48582 (p : Pattern) (ha : d205861 p = 1) (hb : d207424 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d205856 q = 1) (hb : d207419 q = 1) : d0 q = 1 := by
    cases bit : q 253 with
    | false =>
      simp only [d205856, d207419, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48581 q ha hb
    | true =>
      simp only [d205856, d207419, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d205857 q = 1) (hb : d207420 q = 1) : d0 q = 1 := by
    cases bit : q 252 with
    | false =>
      simp only [d205857, d207420, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d205857, d207420, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d205858 q = 1) (hb : d207421 q = 1) : d0 q = 1 := by
    cases bit : q 251 with
    | false =>
      simp only [d205858, d207421, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d205858, d207421, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d205859 q = 1) (hb : d207422 q = 1) : d0 q = 1 := by
    cases bit : q 250 with
    | false =>
      simp only [d205859, d207422, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d205859, d207422, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d205860 q = 1) (hb : d207423 q = 1) : d0 q = 1 := by
    cases bit : q 249 with
    | false =>
      simp only [d205860, d207423, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d205860, d207423, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d205861 q = 1) (hb : d207424 q = 1) : d0 q = 1 := by
    cases bit : q 245 with
    | false =>
      simp only [d205861, d207424, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d205861, d207424, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro48583 (p : Pattern) (ha : d205867 p = 1) (hb : d207430 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d205862 q = 1) (hb : d207425 q = 1) : d0 q = 1 := by
    cases bit : q 200 with
    | false =>
      simp only [d205862, d207425, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48582 q ha hb
    | true =>
      simp only [d205862, d207425, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d205863 q = 1) (hb : d207426 q = 1) : d0 q = 1 := by
    cases bit : q 199 with
    | false =>
      simp only [d205863, d207426, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d205863, d207426, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d205864 q = 1) (hb : d207427 q = 1) : d0 q = 1 := by
    cases bit : q 186 with
    | false =>
      simp only [d205864, d207427, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d205864, d207427, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d205865 q = 1) (hb : d207428 q = 1) : d0 q = 1 := by
    cases bit : q 185 with
    | false =>
      simp only [d205865, d207428, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d205865, d207428, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d205866 q = 1) (hb : d207429 q = 1) : d0 q = 1 := by
    cases bit : q 184 with
    | false =>
      simp only [d205866, d207429, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d205866, d207429, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d205867 q = 1) (hb : d207430 q = 1) : d0 q = 1 := by
    cases bit : q 181 with
    | false =>
      simp only [d205867, d207430, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d205867, d207430, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro48584 (p : Pattern) (ha : d205873 p = 1) (hb : d207436 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d205868 q = 1) (hb : d207431 q = 1) : d0 q = 1 := by
    cases bit : q 177 with
    | false =>
      simp only [d205868, d207431, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48583 q ha hb
    | true =>
      simp only [d205868, d207431, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d205869 q = 1) (hb : d207432 q = 1) : d0 q = 1 := by
    cases bit : q 164 with
    | false =>
      simp only [d205869, d207432, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d205869, d207432, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d205870 q = 1) (hb : d207433 q = 1) : d0 q = 1 := by
    cases bit : q 156 with
    | false =>
      simp only [d205870, d207433, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d205870, d207433, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d205871 q = 1) (hb : d207434 q = 1) : d0 q = 1 := by
    cases bit : q 155 with
    | false =>
      simp only [d205871, d207434, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d205871, d207434, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d205872 q = 1) (hb : d207435 q = 1) : d0 q = 1 := by
    cases bit : q 134 with
    | false =>
      simp only [d205872, d207435, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d205872, d207435, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d205873 q = 1) (hb : d207436 q = 1) : d0 q = 1 := by
    cases bit : q 133 with
    | false =>
      simp only [d205873, d207436, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d205873, d207436, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro48585 (p : Pattern) (ha : d205879 p = 1) (hb : d207442 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d205874 q = 1) (hb : d207437 q = 1) : d0 q = 1 := by
    cases bit : q 120 with
    | false =>
      simp only [d205874, d207437, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48584 q ha hb
    | true =>
      simp only [d205874, d207437, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d205875 q = 1) (hb : d207438 q = 1) : d0 q = 1 := by
    cases bit : q 118 with
    | false =>
      simp only [d205875, d207438, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d205875, d207438, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d205876 q = 1) (hb : d207439 q = 1) : d0 q = 1 := by
    cases bit : q 114 with
    | false =>
      simp only [d205876, d207439, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d205876, d207439, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d205877 q = 1) (hb : d207440 q = 1) : d0 q = 1 := by
    cases bit : q 111 with
    | false =>
      simp only [d205877, d207440, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d205877, d207440, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d205878 q = 1) (hb : d207441 q = 1) : d0 q = 1 := by
    cases bit : q 98 with
    | false =>
      simp only [d205878, d207441, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d205878, d207441, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d205879 q = 1) (hb : d207442 q = 1) : d0 q = 1 := by
    cases bit : q 97 with
    | false =>
      simp only [d205879, d207442, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d205879, d207442, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro48586 (p : Pattern) (ha : d205885 p = 1) (hb : d207448 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d205880 q = 1) (hb : d207443 q = 1) : d0 q = 1 := by
    cases bit : q 94 with
    | false =>
      simp only [d205880, d207443, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48585 q ha hb
    | true =>
      simp only [d205880, d207443, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d205881 q = 1) (hb : d207444 q = 1) : d0 q = 1 := by
    cases bit : q 76 with
    | false =>
      simp only [d205881, d207444, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d205881, d207444, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d205882 q = 1) (hb : d207445 q = 1) : d0 q = 1 := by
    cases bit : q 67 with
    | false =>
      simp only [d205882, d207445, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d205882, d207445, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d205883 q = 1) (hb : d207446 q = 1) : d0 q = 1 := by
    cases bit : q 52 with
    | false =>
      simp only [d205883, d207446, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d205883, d207446, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d205884 q = 1) (hb : d207447 q = 1) : d0 q = 1 := by
    cases bit : q 47 with
    | false =>
      simp only [d205884, d207447, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d205884, d207447, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d205885 q = 1) (hb : d207448 q = 1) : d0 q = 1 := by
    cases bit : q 46 with
    | false =>
      simp only [d205885, d207448, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d205885, d207448, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro48587 (p : Pattern) (ha : d205891 p = 1) (hb : d207454 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d205886 q = 1) (hb : d207449 q = 1) : d0 q = 1 := by
    cases bit : q 45 with
    | false =>
      simp only [d205886, d207449, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48586 q ha hb
    | true =>
      simp only [d205886, d207449, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d205887 q = 1) (hb : d207450 q = 1) : d0 q = 1 := by
    cases bit : q 30 with
    | false =>
      simp only [d205887, d207450, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d205887, d207450, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d205888 q = 1) (hb : d207451 q = 1) : d0 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d205888, d207451, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d205888, d207451, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d205889 q = 1) (hb : d207452 q = 1) : d0 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d205889, d207452, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d205889, d207452, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d205890 q = 1) (hb : d207453 q = 1) : d0 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d205890, d207453, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d205890, d207453, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d205891 q = 1) (hb : d207454 q = 1) : d0 q = 1 := by
    cases bit : q 25 with
    | false =>
      simp only [d205891, d207454, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d205891, d207454, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro48588 (p : Pattern) (ha : d53647 p = 1) (hb : d202307 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d202307 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d112 q = 1) (hb : d202307 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47900 q ha hb
    | true =>
      simp only [d112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47901 q ha hb
  have h2 (q : Pattern) (ha : d113 q = 1) (hb : d202307 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d53637 q = 1) (hb : d202307 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d53637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d53637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d53638 q = 1) (hb : d202307 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d53638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d407 q = 1) (hb : d202307 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47920 q ha hb
  have h6 (q : Pattern) (ha : d53639 q = 1) (hb : d202307 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d53639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d53639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d53640 q = 1) (hb : d202307 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d53640, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d53640, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d53641 q = 1) (hb : d202307 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d53641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d53641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d53642 q = 1) (hb : d202307 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d53642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d53642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d463 q = 1) (hb : d202307 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d463, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d463, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47921 q ha hb
  have h11 (q : Pattern) (ha : d53643 q = 1) (hb : d202307 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d53643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d53643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d53644 q = 1) (hb : d202307 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d53644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d53644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d53645 q = 1) (hb : d202307 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d53645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d53645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d53646 q = 1) (hb : d202307 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d53646, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d53646, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d53647 q = 1) (hb : d202307 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d53647, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d53647, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro48589 (p : Pattern) (ha : d194340 p = 1) (hb : d202307 p = 1) : d206194 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d202307 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d20913 q = 1) (hb : d202307 q = 1) : d205920 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d20913, d205920, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47912 q ha hb
    | true =>
      simp only [d20913, d205920, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47892 q ha hb
  have h2 (q : Pattern) (ha : d20969 q = 1) (hb : d202307 q = 1) : d205978 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d20969, d205978, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20969, d205978, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d20970 q = 1) (hb : d202307 q = 1) : d205979 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d20970, d205979, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d20970, d205979, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d20971 q = 1) (hb : d202307 q = 1) : d205980 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d20971, d205980, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20971, d205980, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d20972 q = 1) (hb : d202307 q = 1) : d205981 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d20972, d205981, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20972, d205981, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d194340 q = 1) (hb : d202307 q = 1) : d206194 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d194340, d206194, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d194340, d206194, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro48590 (p : Pattern) (ha : d194350 p = 1) (hb : d202307 p = 1) : d206240 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d202307 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d20945 q = 1) (hb : d202307 q = 1) : d205954 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d20945, d205954, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47917 q ha hb
    | true =>
      simp only [d20945, d205954, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47897 q ha hb
  have h2 (q : Pattern) (ha : d194346 q = 1) (hb : d202307 q = 1) : d206236 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d194346, d206236, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d194346, d206236, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d194347 q = 1) (hb : d202307 q = 1) : d206237 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d194347, d206237, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d194347, d206237, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d194348 q = 1) (hb : d202307 q = 1) : d206238 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d194348, d206238, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d194348, d206238, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d194349 q = 1) (hb : d202307 q = 1) : d206239 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d194349, d206239, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d194349, d206239, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d194350 q = 1) (hb : d202307 q = 1) : d206240 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d194350, d206240, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d194350, d206240, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro48591 (p : Pattern) (ha : d194356 p = 1) (hb : d202307 p = 1) : d207465 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d202307 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d20974 q = 1) (hb : d202307 q = 1) : d205983 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d20974, d205983, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47922 q ha hb
    | true =>
      simp only [d20974, d205983, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47923 q ha hb
  have h2 (q : Pattern) (ha : d20975 q = 1) (hb : d202307 q = 1) : d205984 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d20975, d205984, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d20975, d205984, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d194338 q = 1) (hb : d202307 q = 1) : d207455 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d194338, d207455, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d194338, d207455, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d194339 q = 1) (hb : d202307 q = 1) : d207456 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d194339, d207456, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d194339, d207456, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d194341 q = 1) (hb : d202307 q = 1) : d206195 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d194341, d206195, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d194341, d206195, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48589 q ha hb
  have h6 (q : Pattern) (ha : d194342 q = 1) (hb : d202307 q = 1) : d207457 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d194342, d207457, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d194342, d207457, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d194343 q = 1) (hb : d202307 q = 1) : d207458 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d194343, d207458, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d194343, d207458, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d194344 q = 1) (hb : d202307 q = 1) : d207459 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d194344, d207459, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d194344, d207459, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d194345 q = 1) (hb : d202307 q = 1) : d207460 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d194345, d207460, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d194345, d207460, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d194351 q = 1) (hb : d202307 q = 1) : d206241 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d194351, d206241, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d194351, d206241, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48590 q ha hb
  have h11 (q : Pattern) (ha : d194352 q = 1) (hb : d202307 q = 1) : d207461 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d194352, d207461, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d194352, d207461, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d194353 q = 1) (hb : d202307 q = 1) : d207462 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d194353, d207462, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d194353, d207462, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d194354 q = 1) (hb : d202307 q = 1) : d207463 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d194354, d207463, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d194354, d207463, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d194355 q = 1) (hb : d202307 q = 1) : d207464 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d194355, d207464, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d194355, d207464, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d194356 q = 1) (hb : d202307 q = 1) : d207465 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d194356, d207465, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d194356, d207465, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro48592 (p : Pattern) (ha : d194362 p = 1) (hb : d202307 p = 1) : d207471 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d202307 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d53648 q = 1) (hb : d202307 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d53648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48588 q ha hb
  have h2 (q : Pattern) (ha : d53649 q = 1) (hb : d202307 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d53649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d53650 q = 1) (hb : d202307 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d53650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d53651 q = 1) (hb : d202307 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d53651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d53652 q = 1) (hb : d202307 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d53652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d194357 q = 1) (hb : d202307 q = 1) : d207466 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d194357, d207466, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d194357, d207466, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48591 q ha hb
  have h7 (q : Pattern) (ha : d194358 q = 1) (hb : d202307 q = 1) : d207467 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d194358, d207467, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d194358, d207467, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d194359 q = 1) (hb : d202307 q = 1) : d207468 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d194359, d207468, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d194359, d207468, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d194360 q = 1) (hb : d202307 q = 1) : d207469 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d194360, d207469, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d194360, d207469, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d194361 q = 1) (hb : d202307 q = 1) : d207470 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d194361, d207470, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d194361, d207470, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d194362 q = 1) (hb : d202307 q = 1) : d207471 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d194362, d207471, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d194362, d207471, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro48593 (p : Pattern) (ha : d194365 p = 1) (hb : d202307 p = 1) : d207474 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d202307 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d21156 q = 1) (hb : d202307 q = 1) : d206036 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d21156, d206036, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47953 q ha hb
    | true =>
      simp only [d21156, d206036, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47954 q ha hb
  have h2 (q : Pattern) (ha : d21157 q = 1) (hb : d202307 q = 1) : d206099 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d21157, d206099, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21157, d206099, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d21158 q = 1) (hb : d202307 q = 1) : d206100 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d21158, d206100, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d21158, d206100, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d21159 q = 1) (hb : d202307 q = 1) : d206101 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d21159, d206101, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21159, d206101, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d21160 q = 1) (hb : d202307 q = 1) : d206102 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d21160, d206102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21160, d206102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d194365 q = 1) (hb : d202307 q = 1) : d207474 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d194365, d207474, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d194365, d207474, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro48594 (p : Pattern) (ha : d194376 p = 1) (hb : d202307 p = 1) : d207484 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d202307 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d194371 q = 1) (hb : d202307 q = 1) : d206074 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d194371, d206074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47989 q ha hb
    | true =>
      simp only [d194371, d206074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47960 q ha hb
  have h2 (q : Pattern) (ha : d194372 q = 1) (hb : d202307 q = 1) : d207480 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d194372, d207480, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d194372, d207480, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d194373 q = 1) (hb : d202307 q = 1) : d207481 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d194373, d207481, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d194373, d207481, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d194374 q = 1) (hb : d202307 q = 1) : d207482 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d194374, d207482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d194374, d207482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d194375 q = 1) (hb : d202307 q = 1) : d207483 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d194375, d207483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d194375, d207483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d194376 q = 1) (hb : d202307 q = 1) : d207484 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d194376, d207484, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d194376, d207484, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro48595 (p : Pattern) (ha : d194382 p = 1) (hb : d202307 p = 1) : d207490 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d202307 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d21162 q = 1) (hb : d202307 q = 1) : d206104 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d21162, d206104, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47952 q ha hb
    | true =>
      simp only [d21162, d206104, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47955 q ha hb
  have h2 (q : Pattern) (ha : d21163 q = 1) (hb : d202307 q = 1) : d206105 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d21163, d206105, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d21163, d206105, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d194363 q = 1) (hb : d202307 q = 1) : d207472 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d194363, d207472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d194363, d207472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d194364 q = 1) (hb : d202307 q = 1) : d207473 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d194364, d207473, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d194364, d207473, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d194366 q = 1) (hb : d202307 q = 1) : d207475 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d194366, d207475, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d194366, d207475, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48593 q ha hb
  have h6 (q : Pattern) (ha : d194367 q = 1) (hb : d202307 q = 1) : d207476 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d194367, d207476, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d194367, d207476, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d194368 q = 1) (hb : d202307 q = 1) : d207477 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d194368, d207477, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d194368, d207477, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d194369 q = 1) (hb : d202307 q = 1) : d207478 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d194369, d207478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d194369, d207478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d194370 q = 1) (hb : d202307 q = 1) : d207479 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d194370, d207479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d194370, d207479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d194377 q = 1) (hb : d202307 q = 1) : d207485 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d194377, d207485, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d194377, d207485, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48594 q ha hb
  have h11 (q : Pattern) (ha : d194378 q = 1) (hb : d202307 q = 1) : d207486 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d194378, d207486, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d194378, d207486, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d194379 q = 1) (hb : d202307 q = 1) : d207487 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d194379, d207487, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d194379, d207487, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d194380 q = 1) (hb : d202307 q = 1) : d207488 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d194380, d207488, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d194380, d207488, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d194381 q = 1) (hb : d202307 q = 1) : d207489 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d194381, d207489, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d194381, d207489, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d194382 q = 1) (hb : d202307 q = 1) : d207490 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d194382, d207490, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d194382, d207490, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro48596 (p : Pattern) (ha : d194388 p = 1) (hb : d202307 p = 1) : d207496 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d202307 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d194383 q = 1) (hb : d202307 q = 1) : d207491 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d194383, d207491, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d194383, d207491, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48595 q ha hb
  have h2 (q : Pattern) (ha : d194384 q = 1) (hb : d202307 q = 1) : d207492 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d194384, d207492, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d194384, d207492, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d194385 q = 1) (hb : d202307 q = 1) : d207493 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d194385, d207493, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d194385, d207493, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d194386 q = 1) (hb : d202307 q = 1) : d207494 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d194386, d207494, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d194386, d207494, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d194387 q = 1) (hb : d202307 q = 1) : d207495 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d194387, d207495, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d194387, d207495, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d194388 q = 1) (hb : d202307 q = 1) : d207496 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d194388, d207496, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d194388, d207496, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro48597 (p : Pattern) (ha : d194392 p = 1) (hb : d202307 p = 1) : d207500 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d202307 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d21455 q = 1) (hb : d202307 q = 1) : d206281 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d21455, d206281, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48002 q ha hb
    | true =>
      simp only [d21455, d206281, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48003 q ha hb
  have h2 (q : Pattern) (ha : d21456 q = 1) (hb : d202307 q = 1) : d206282 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d21456, d206282, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21456, d206282, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d21457 q = 1) (hb : d202307 q = 1) : d206283 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d21457, d206283, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d21457, d206283, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d21458 q = 1) (hb : d202307 q = 1) : d206284 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d21458, d206284, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21458, d206284, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d21459 q = 1) (hb : d202307 q = 1) : d206285 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d21459, d206285, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21459, d206285, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d194392 q = 1) (hb : d202307 q = 1) : d207500 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d194392, d207500, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d194392, d207500, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro48598 (p : Pattern) (ha : d194403 p = 1) (hb : d202307 p = 1) : d207511 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d202307 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d194398 q = 1) (hb : d202307 q = 1) : d207506 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d194398, d207506, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48042 q ha hb
    | true =>
      simp only [d194398, d207506, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48011 q ha hb
  have h2 (q : Pattern) (ha : d194399 q = 1) (hb : d202307 q = 1) : d207507 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d194399, d207507, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d194399, d207507, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d194400 q = 1) (hb : d202307 q = 1) : d207508 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d194400, d207508, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d194400, d207508, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d194401 q = 1) (hb : d202307 q = 1) : d207509 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d194401, d207509, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d194401, d207509, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d194402 q = 1) (hb : d202307 q = 1) : d207510 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d194402, d207510, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d194402, d207510, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d194403 q = 1) (hb : d202307 q = 1) : d207511 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d194403, d207511, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d194403, d207511, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro48599 (p : Pattern) (ha : d194409 p = 1) (hb : d202307 p = 1) : d207517 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d202307 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d21461 q = 1) (hb : d202307 q = 1) : d206287 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d21461, d206287, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48001 q ha hb
    | true =>
      simp only [d21461, d206287, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48004 q ha hb
  have h2 (q : Pattern) (ha : d21462 q = 1) (hb : d202307 q = 1) : d206288 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d21462, d206288, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d21462, d206288, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d194390 q = 1) (hb : d202307 q = 1) : d207498 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d194390, d207498, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d194390, d207498, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d194391 q = 1) (hb : d202307 q = 1) : d207499 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d194391, d207499, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d194391, d207499, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d194393 q = 1) (hb : d202307 q = 1) : d207501 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d194393, d207501, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d194393, d207501, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48597 q ha hb
  have h6 (q : Pattern) (ha : d194394 q = 1) (hb : d202307 q = 1) : d207502 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d194394, d207502, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d194394, d207502, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d194395 q = 1) (hb : d202307 q = 1) : d207503 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d194395, d207503, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d194395, d207503, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d194396 q = 1) (hb : d202307 q = 1) : d207504 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d194396, d207504, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d194396, d207504, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d194397 q = 1) (hb : d202307 q = 1) : d207505 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d194397, d207505, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d194397, d207505, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d194404 q = 1) (hb : d202307 q = 1) : d207512 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d194404, d207512, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d194404, d207512, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48598 q ha hb
  have h11 (q : Pattern) (ha : d194405 q = 1) (hb : d202307 q = 1) : d207513 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d194405, d207513, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d194405, d207513, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d194406 q = 1) (hb : d202307 q = 1) : d207514 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d194406, d207514, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d194406, d207514, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d194407 q = 1) (hb : d202307 q = 1) : d207515 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d194407, d207515, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d194407, d207515, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d194408 q = 1) (hb : d202307 q = 1) : d207516 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d194408, d207516, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d194408, d207516, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d194409 q = 1) (hb : d202307 q = 1) : d207517 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d194409, d207517, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d194409, d207517, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro48600 (p : Pattern) (ha : d194415 p = 1) (hb : d202307 p = 1) : d207523 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d202307 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d194410 q = 1) (hb : d202307 q = 1) : d207518 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d194410, d207518, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d194410, d207518, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48599 q ha hb
  have h2 (q : Pattern) (ha : d194411 q = 1) (hb : d202307 q = 1) : d207519 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d194411, d207519, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d194411, d207519, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d194412 q = 1) (hb : d202307 q = 1) : d207520 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d194412, d207520, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d194412, d207520, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d194413 q = 1) (hb : d202307 q = 1) : d207521 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d194413, d207521, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d194413, d207521, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d194414 q = 1) (hb : d202307 q = 1) : d207522 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d194414, d207522, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d194414, d207522, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d194415 q = 1) (hb : d202307 q = 1) : d207523 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d194415, d207523, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d194415, d207523, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro48601 (p : Pattern) (ha : d194420 p = 1) (hb : d202307 p = 1) : d207528 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d202307 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d21808 q = 1) (hb : d202307 q = 1) : d206555 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d21808, d206555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48065 q ha hb
    | true =>
      simp only [d21808, d206555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48066 q ha hb
  have h2 (q : Pattern) (ha : d21809 q = 1) (hb : d202307 q = 1) : d206556 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d21809, d206556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21809, d206556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d21810 q = 1) (hb : d202307 q = 1) : d206557 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d21810, d206557, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d21810, d206557, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d21811 q = 1) (hb : d202307 q = 1) : d206558 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d21811, d206558, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21811, d206558, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d21812 q = 1) (hb : d202307 q = 1) : d206559 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d21812, d206559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21812, d206559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d194420 q = 1) (hb : d202307 q = 1) : d207528 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d194420, d207528, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d194420, d207528, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro48602 (p : Pattern) (ha : d194427 p = 1) (hb : d202307 p = 1) : d206770 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d202307 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d22070 q = 1) (hb : d202307 q = 1) : d206727 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d22070, d206727, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48105 q ha hb
    | true =>
      simp only [d22070, d206727, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48073 q ha hb
  have h2 (q : Pattern) (ha : d22071 q = 1) (hb : d202307 q = 1) : d206728 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d22071, d206728, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22071, d206728, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d22072 q = 1) (hb : d202307 q = 1) : d206729 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d22072, d206729, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22072, d206729, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d22079 q = 1) (hb : d202307 q = 1) : d206736 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d22079, d206736, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48073 q ha hb
    | true =>
      simp only [d22079, d206736, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48107 q ha hb
  have h5 (q : Pattern) (ha : d22080 q = 1) (hb : d202307 q = 1) : d206737 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d22080, d206737, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22080, d206737, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d22081 q = 1) (hb : d202307 q = 1) : d206738 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d22081, d206738, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22081, d206738, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d22082 q = 1) (hb : d202307 q = 1) : d206739 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d22082, d206739, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d22082, d206739, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d22098 q = 1) (hb : d202307 q = 1) : d206755 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d22098, d206755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48073 q ha hb
    | true =>
      simp only [d22098, d206755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48074 q ha hb
  have h9 (q : Pattern) (ha : d22099 q = 1) (hb : d202307 q = 1) : d206756 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d22099, d206756, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22099, d206756, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d22100 q = 1) (hb : d202307 q = 1) : d206757 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d22100, d206757, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22100, d206757, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d22101 q = 1) (hb : d202307 q = 1) : d206758 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d22101, d206758, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d22101, d206758, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d194426 q = 1) (hb : d202307 q = 1) : d206769 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d194426, d206769, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d194426, d206769, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d194427 q = 1) (hb : d202307 q = 1) : d206770 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d194427, d206770, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d194427, d206770, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h13 p ha hb
theorem andIntro48603 (p : Pattern) (ha : d194433 p = 1) (hb : d202307 p = 1) : d207537 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d202307 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d194428 q = 1) (hb : d202307 q = 1) : d206771 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d194428, d206771, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48602 q ha hb
    | true =>
      simp only [d194428, d206771, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d194429 q = 1) (hb : d202307 q = 1) : d206772 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d194429, d206772, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d194429, d206772, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d22104 q = 1) (hb : d202307 q = 1) : d206761 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d22104, d206761, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48075 q ha hb
    | true =>
      simp only [d22104, d206761, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d22105 q = 1) (hb : d202307 q = 1) : d206762 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d22105, d206762, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22105, d206762, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d194430 q = 1) (hb : d202307 q = 1) : d207534 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d194430, d207534, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d194430, d207534, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d194431 q = 1) (hb : d202307 q = 1) : d207535 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d194431, d207535, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d194431, d207535, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d194432 q = 1) (hb : d202307 q = 1) : d207536 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d194432, d207536, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d194432, d207536, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d194433 q = 1) (hb : d202307 q = 1) : d207537 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d194433, d207537, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d194433, d207537, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro48604 (p : Pattern) (ha : d194439 p = 1) (hb : d202307 p = 1) : d207543 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d202307 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d194434 q = 1) (hb : d202307 q = 1) : d207538 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d194434, d207538, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48603 q ha hb
    | true =>
      simp only [d194434, d207538, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48076 q ha hb
  have h2 (q : Pattern) (ha : d194435 q = 1) (hb : d202307 q = 1) : d207539 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d194435, d207539, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d194435, d207539, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d194436 q = 1) (hb : d202307 q = 1) : d207540 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d194436, d207540, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d194436, d207540, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d194437 q = 1) (hb : d202307 q = 1) : d207541 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d194437, d207541, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d194437, d207541, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d194438 q = 1) (hb : d202307 q = 1) : d207542 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d194438, d207542, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d194438, d207542, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d194439 q = 1) (hb : d202307 q = 1) : d207543 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d194439, d207543, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d194439, d207543, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro48605 (p : Pattern) (ha : d194445 p = 1) (hb : d202307 p = 1) : d207549 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d202307 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d21814 q = 1) (hb : d202307 q = 1) : d206561 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d21814, d206561, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48064 q ha hb
    | true =>
      simp only [d21814, d206561, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48067 q ha hb
  have h2 (q : Pattern) (ha : d21815 q = 1) (hb : d202307 q = 1) : d206562 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d21815, d206562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d21815, d206562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d194418 q = 1) (hb : d202307 q = 1) : d207526 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d194418, d207526, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d194418, d207526, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d194419 q = 1) (hb : d202307 q = 1) : d207527 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d194419, d207527, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d194419, d207527, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d194421 q = 1) (hb : d202307 q = 1) : d207529 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d194421, d207529, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d194421, d207529, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48601 q ha hb
  have h6 (q : Pattern) (ha : d194422 q = 1) (hb : d202307 q = 1) : d207530 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d194422, d207530, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d194422, d207530, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d194423 q = 1) (hb : d202307 q = 1) : d207531 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d194423, d207531, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d194423, d207531, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d194424 q = 1) (hb : d202307 q = 1) : d207532 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d194424, d207532, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d194424, d207532, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d194425 q = 1) (hb : d202307 q = 1) : d207533 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d194425, d207533, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d194425, d207533, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d194440 q = 1) (hb : d202307 q = 1) : d207544 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d194440, d207544, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d194440, d207544, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48604 q ha hb
  have h11 (q : Pattern) (ha : d194441 q = 1) (hb : d202307 q = 1) : d207545 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d194441, d207545, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d194441, d207545, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d194442 q = 1) (hb : d202307 q = 1) : d207546 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d194442, d207546, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d194442, d207546, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d194443 q = 1) (hb : d202307 q = 1) : d207547 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d194443, d207547, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d194443, d207547, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d194444 q = 1) (hb : d202307 q = 1) : d207548 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d194444, d207548, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d194444, d207548, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d194445 q = 1) (hb : d202307 q = 1) : d207549 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d194445, d207549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d194445, d207549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro48606 (p : Pattern) (ha : d194451 p = 1) (hb : d202307 p = 1) : d207555 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d202307 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d194446 q = 1) (hb : d202307 q = 1) : d207550 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d194446, d207550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d194446, d207550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48605 q ha hb
  have h2 (q : Pattern) (ha : d194447 q = 1) (hb : d202307 q = 1) : d207551 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d194447, d207551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d194447, d207551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d194448 q = 1) (hb : d202307 q = 1) : d207552 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d194448, d207552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d194448, d207552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d194449 q = 1) (hb : d202307 q = 1) : d207553 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d194449, d207553, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d194449, d207553, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d194450 q = 1) (hb : d202307 q = 1) : d207554 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d194450, d207554, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d194450, d207554, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d194451 q = 1) (hb : d202307 q = 1) : d207555 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d194451, d207555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d194451, d207555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro48607 (p : Pattern) (ha : d194457 p = 1) (hb : d202307 p = 1) : d207561 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d202307 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d22286 q = 1) (hb : d202307 q = 1) : d206883 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d22286, d206883, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48141 q ha hb
    | true =>
      simp only [d22286, d206883, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48142 q ha hb
  have h2 (q : Pattern) (ha : d22287 q = 1) (hb : d202307 q = 1) : d206884 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d22287, d206884, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22287, d206884, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d22288 q = 1) (hb : d202307 q = 1) : d206885 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d22288, d206885, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d22288, d206885, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d22289 q = 1) (hb : d202307 q = 1) : d206886 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d22289, d206886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22289, d206886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d22290 q = 1) (hb : d202307 q = 1) : d206887 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d22290, d206887, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22290, d206887, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d194457 q = 1) (hb : d202307 q = 1) : d207561 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d194457, d207561, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d194457, d207561, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro48608 (p : Pattern) (ha : d194464 p = 1) (hb : d202307 p = 1) : d207082 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d202307 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d22535 q = 1) (hb : d202307 q = 1) : d207039 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d22535, d207039, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48181 q ha hb
    | true =>
      simp only [d22535, d207039, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48149 q ha hb
  have h2 (q : Pattern) (ha : d22536 q = 1) (hb : d202307 q = 1) : d207040 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d22536, d207040, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22536, d207040, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d22537 q = 1) (hb : d202307 q = 1) : d207041 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d22537, d207041, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22537, d207041, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d22544 q = 1) (hb : d202307 q = 1) : d207048 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d22544, d207048, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48149 q ha hb
    | true =>
      simp only [d22544, d207048, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48183 q ha hb
  have h5 (q : Pattern) (ha : d22545 q = 1) (hb : d202307 q = 1) : d207049 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d22545, d207049, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22545, d207049, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d22546 q = 1) (hb : d202307 q = 1) : d207050 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d22546, d207050, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22546, d207050, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d22547 q = 1) (hb : d202307 q = 1) : d207051 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d22547, d207051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d22547, d207051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d22563 q = 1) (hb : d202307 q = 1) : d207067 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d22563, d207067, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48149 q ha hb
    | true =>
      simp only [d22563, d207067, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48150 q ha hb
  have h9 (q : Pattern) (ha : d22564 q = 1) (hb : d202307 q = 1) : d207068 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d22564, d207068, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22564, d207068, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d22565 q = 1) (hb : d202307 q = 1) : d207069 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d22565, d207069, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22565, d207069, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d22566 q = 1) (hb : d202307 q = 1) : d207070 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d22566, d207070, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d22566, d207070, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d194463 q = 1) (hb : d202307 q = 1) : d207081 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d194463, d207081, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d194463, d207081, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d194464 q = 1) (hb : d202307 q = 1) : d207082 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d194464, d207082, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d194464, d207082, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h13 p ha hb
theorem andIntro48609 (p : Pattern) (ha : d194470 p = 1) (hb : d202307 p = 1) : d207570 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d202307 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d194465 q = 1) (hb : d202307 q = 1) : d207083 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d194465, d207083, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48608 q ha hb
    | true =>
      simp only [d194465, d207083, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d194466 q = 1) (hb : d202307 q = 1) : d207084 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d194466, d207084, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d194466, d207084, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d22569 q = 1) (hb : d202307 q = 1) : d207073 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d22569, d207073, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48151 q ha hb
    | true =>
      simp only [d22569, d207073, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d22570 q = 1) (hb : d202307 q = 1) : d207074 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d22570, d207074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22570, d207074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d194467 q = 1) (hb : d202307 q = 1) : d207567 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d194467, d207567, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d194467, d207567, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d194468 q = 1) (hb : d202307 q = 1) : d207568 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d194468, d207568, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d194468, d207568, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d194469 q = 1) (hb : d202307 q = 1) : d207569 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d194469, d207569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d194469, d207569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d194470 q = 1) (hb : d202307 q = 1) : d207570 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d194470, d207570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d194470, d207570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro48610 (p : Pattern) (ha : d194476 p = 1) (hb : d202307 p = 1) : d207576 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d202307 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d194471 q = 1) (hb : d202307 q = 1) : d207571 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d194471, d207571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48609 q ha hb
    | true =>
      simp only [d194471, d207571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48152 q ha hb
  have h2 (q : Pattern) (ha : d194472 q = 1) (hb : d202307 q = 1) : d207572 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d194472, d207572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d194472, d207572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d194473 q = 1) (hb : d202307 q = 1) : d207573 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d194473, d207573, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d194473, d207573, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d194474 q = 1) (hb : d202307 q = 1) : d207574 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d194474, d207574, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d194474, d207574, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d194475 q = 1) (hb : d202307 q = 1) : d207575 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d194475, d207575, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d194475, d207575, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d194476 q = 1) (hb : d202307 q = 1) : d207576 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d194476, d207576, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d194476, d207576, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro48611 (p : Pattern) (ha : d194482 p = 1) (hb : d202307 p = 1) : d207582 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d202307 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d22292 q = 1) (hb : d202307 q = 1) : d206889 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d22292, d206889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48140 q ha hb
    | true =>
      simp only [d22292, d206889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48143 q ha hb
  have h2 (q : Pattern) (ha : d22293 q = 1) (hb : d202307 q = 1) : d206890 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d22293, d206890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d22293, d206890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d194455 q = 1) (hb : d202307 q = 1) : d207559 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d194455, d207559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d194455, d207559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d194456 q = 1) (hb : d202307 q = 1) : d207560 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d194456, d207560, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d194456, d207560, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d194458 q = 1) (hb : d202307 q = 1) : d207562 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d194458, d207562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d194458, d207562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48607 q ha hb
  have h6 (q : Pattern) (ha : d194459 q = 1) (hb : d202307 q = 1) : d207563 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d194459, d207563, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d194459, d207563, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d194460 q = 1) (hb : d202307 q = 1) : d207564 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d194460, d207564, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d194460, d207564, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d194461 q = 1) (hb : d202307 q = 1) : d207565 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d194461, d207565, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d194461, d207565, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d194462 q = 1) (hb : d202307 q = 1) : d207566 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d194462, d207566, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d194462, d207566, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d194477 q = 1) (hb : d202307 q = 1) : d207577 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d194477, d207577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d194477, d207577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48610 q ha hb
  have h11 (q : Pattern) (ha : d194478 q = 1) (hb : d202307 q = 1) : d207578 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d194478, d207578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d194478, d207578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d194479 q = 1) (hb : d202307 q = 1) : d207579 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d194479, d207579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d194479, d207579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d194480 q = 1) (hb : d202307 q = 1) : d207580 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d194480, d207580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d194480, d207580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d194481 q = 1) (hb : d202307 q = 1) : d207581 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d194481, d207581, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d194481, d207581, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d194482 q = 1) (hb : d202307 q = 1) : d207582 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d194482, d207582, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d194482, d207582, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro48612 (p : Pattern) (ha : d194488 p = 1) (hb : d202307 p = 1) : d207588 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d202307 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d194483 q = 1) (hb : d202307 q = 1) : d207583 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d194483, d207583, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d194483, d207583, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48611 q ha hb
  have h2 (q : Pattern) (ha : d194484 q = 1) (hb : d202307 q = 1) : d207584 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d194484, d207584, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d194484, d207584, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d194485 q = 1) (hb : d202307 q = 1) : d207585 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d194485, d207585, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d194485, d207585, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d194486 q = 1) (hb : d202307 q = 1) : d207586 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d194486, d207586, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d194486, d207586, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d194487 q = 1) (hb : d202307 q = 1) : d207587 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d194487, d207587, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d194487, d207587, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d194488 q = 1) (hb : d202307 q = 1) : d207588 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d194488, d207588, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d194488, d207588, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro48613 (p : Pattern) (ha : d194495 p = 1) (hb : d202307 p = 1) : d207595 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d202307 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d22741 q = 1) (hb : d202307 q = 1) : d207193 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d22741, d207193, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48218 q ha hb
    | true =>
      simp only [d22741, d207193, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48219 q ha hb
  have h2 (q : Pattern) (ha : d22742 q = 1) (hb : d202307 q = 1) : d207194 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d22742, d207194, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22742, d207194, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d22743 q = 1) (hb : d202307 q = 1) : d207195 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d22743, d207195, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d22743, d207195, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d22744 q = 1) (hb : d202307 q = 1) : d207196 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d22744, d207196, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22744, d207196, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d22745 q = 1) (hb : d202307 q = 1) : d207197 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d22745, d207197, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22745, d207197, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d194495 q = 1) (hb : d202307 q = 1) : d207595 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d194495, d207595, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d194495, d207595, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro48614 (p : Pattern) (ha : d194502 p = 1) (hb : d202307 p = 1) : d207371 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d202307 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d22949 q = 1) (hb : d202307 q = 1) : d207328 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d22949, d207328, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48253 q ha hb
    | true =>
      simp only [d22949, d207328, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48226 q ha hb
  have h2 (q : Pattern) (ha : d22950 q = 1) (hb : d202307 q = 1) : d207329 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d22950, d207329, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22950, d207329, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d22951 q = 1) (hb : d202307 q = 1) : d207330 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d22951, d207330, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22951, d207330, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d22958 q = 1) (hb : d202307 q = 1) : d207337 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d22958, d207337, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48226 q ha hb
    | true =>
      simp only [d22958, d207337, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48255 q ha hb
  have h5 (q : Pattern) (ha : d22959 q = 1) (hb : d202307 q = 1) : d207338 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d22959, d207338, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22959, d207338, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d22960 q = 1) (hb : d202307 q = 1) : d207339 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d22960, d207339, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22960, d207339, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d22961 q = 1) (hb : d202307 q = 1) : d207340 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d22961, d207340, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d22961, d207340, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d22977 q = 1) (hb : d202307 q = 1) : d207356 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d22977, d207356, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48226 q ha hb
    | true =>
      simp only [d22977, d207356, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48227 q ha hb
  have h9 (q : Pattern) (ha : d22978 q = 1) (hb : d202307 q = 1) : d207357 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d22978, d207357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22978, d207357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d22979 q = 1) (hb : d202307 q = 1) : d207358 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d22979, d207358, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22979, d207358, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d22980 q = 1) (hb : d202307 q = 1) : d207359 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d22980, d207359, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d22980, d207359, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d194501 q = 1) (hb : d202307 q = 1) : d207370 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d194501, d207370, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d194501, d207370, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d194502 q = 1) (hb : d202307 q = 1) : d207371 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d194502, d207371, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d194502, d207371, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h13 p ha hb
theorem andIntro48615 (p : Pattern) (ha : d194508 p = 1) (hb : d202307 p = 1) : d207604 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d202307 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d194503 q = 1) (hb : d202307 q = 1) : d207372 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d194503, d207372, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48614 q ha hb
    | true =>
      simp only [d194503, d207372, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d194504 q = 1) (hb : d202307 q = 1) : d207373 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d194504, d207373, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d194504, d207373, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d22983 q = 1) (hb : d202307 q = 1) : d207362 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d22983, d207362, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48228 q ha hb
    | true =>
      simp only [d22983, d207362, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d22984 q = 1) (hb : d202307 q = 1) : d207363 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d22984, d207363, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22984, d207363, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d194505 q = 1) (hb : d202307 q = 1) : d207601 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d194505, d207601, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d194505, d207601, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d194506 q = 1) (hb : d202307 q = 1) : d207602 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d194506, d207602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d194506, d207602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d194507 q = 1) (hb : d202307 q = 1) : d207603 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d194507, d207603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d194507, d207603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d194508 q = 1) (hb : d202307 q = 1) : d207604 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d194508, d207604, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d194508, d207604, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro48616 (p : Pattern) (ha : d194514 p = 1) (hb : d202307 p = 1) : d207610 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d202307 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d194509 q = 1) (hb : d202307 q = 1) : d207605 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d194509, d207605, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48615 q ha hb
    | true =>
      simp only [d194509, d207605, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48229 q ha hb
  have h2 (q : Pattern) (ha : d194510 q = 1) (hb : d202307 q = 1) : d207606 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d194510, d207606, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d194510, d207606, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d194511 q = 1) (hb : d202307 q = 1) : d207607 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d194511, d207607, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d194511, d207607, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d194512 q = 1) (hb : d202307 q = 1) : d207608 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d194512, d207608, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d194512, d207608, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d194513 q = 1) (hb : d202307 q = 1) : d207609 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d194513, d207609, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d194513, d207609, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d194514 q = 1) (hb : d202307 q = 1) : d207610 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d194514, d207610, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d194514, d207610, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro48617 (p : Pattern) (ha : d194520 p = 1) (hb : d202307 p = 1) : d207616 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d202307 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d22747 q = 1) (hb : d202307 q = 1) : d207199 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d22747, d207199, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48217 q ha hb
    | true =>
      simp only [d22747, d207199, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48220 q ha hb
  have h2 (q : Pattern) (ha : d22748 q = 1) (hb : d202307 q = 1) : d207200 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d22748, d207200, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d22748, d207200, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d194493 q = 1) (hb : d202307 q = 1) : d207593 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d194493, d207593, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d194493, d207593, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d194494 q = 1) (hb : d202307 q = 1) : d207594 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d194494, d207594, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d194494, d207594, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d194496 q = 1) (hb : d202307 q = 1) : d207596 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d194496, d207596, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d194496, d207596, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48613 q ha hb
  have h6 (q : Pattern) (ha : d194497 q = 1) (hb : d202307 q = 1) : d207597 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d194497, d207597, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d194497, d207597, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d194498 q = 1) (hb : d202307 q = 1) : d207598 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d194498, d207598, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d194498, d207598, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d194499 q = 1) (hb : d202307 q = 1) : d207599 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d194499, d207599, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d194499, d207599, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d194500 q = 1) (hb : d202307 q = 1) : d207600 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d194500, d207600, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d194500, d207600, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d194515 q = 1) (hb : d202307 q = 1) : d207611 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d194515, d207611, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d194515, d207611, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48616 q ha hb
  have h11 (q : Pattern) (ha : d194516 q = 1) (hb : d202307 q = 1) : d207612 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d194516, d207612, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d194516, d207612, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d194517 q = 1) (hb : d202307 q = 1) : d207613 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d194517, d207613, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d194517, d207613, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d194518 q = 1) (hb : d202307 q = 1) : d207614 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d194518, d207614, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d194518, d207614, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d194519 q = 1) (hb : d202307 q = 1) : d207615 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d194519, d207615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d194519, d207615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d194520 q = 1) (hb : d202307 q = 1) : d207616 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d194520, d207616, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d194520, d207616, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro48618 (p : Pattern) (ha : d194526 p = 1) (hb : d202307 p = 1) : d207622 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d202307 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d194521 q = 1) (hb : d202307 q = 1) : d207617 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d194521, d207617, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d194521, d207617, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48617 q ha hb
  have h2 (q : Pattern) (ha : d194522 q = 1) (hb : d202307 q = 1) : d207618 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d194522, d207618, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d194522, d207618, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d194523 q = 1) (hb : d202307 q = 1) : d207619 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d194523, d207619, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d194523, d207619, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d194524 q = 1) (hb : d202307 q = 1) : d207620 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d194524, d207620, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d194524, d207620, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d194525 q = 1) (hb : d202307 q = 1) : d207621 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d194525, d207621, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d194525, d207621, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d194526 q = 1) (hb : d202307 q = 1) : d207622 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d194526, d207622, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d194526, d207622, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro48619 (p : Pattern) (ha : d194532 p = 1) (hb : d202307 p = 1) : d207628 p = 1 := by
  have h0 (q : Pattern) (ha : d194389 q = 1) (hb : d202307 q = 1) : d207497 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d194389, d207497, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48592 q ha hb
    | true =>
      simp only [d194389, d207497, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48596 q ha hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d202307 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d194416 q = 1) (hb : d202307 q = 1) : d207524 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d194416, d207524, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d194416, d207524, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48600 q ha hb
  have h3 (q : Pattern) (ha : d194417 q = 1) (hb : d202307 q = 1) : d207525 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d194417, d207525, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d194417, d207525, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d194452 q = 1) (hb : d202307 q = 1) : d207556 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d194452, d207556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d194452, d207556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48606 q ha hb
  have h5 (q : Pattern) (ha : d194453 q = 1) (hb : d202307 q = 1) : d207557 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d194453, d207557, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d194453, d207557, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d194454 q = 1) (hb : d202307 q = 1) : d207558 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d194454, d207558, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d194454, d207558, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d194489 q = 1) (hb : d202307 q = 1) : d207589 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d194489, d207589, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d194489, d207589, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48612 q ha hb
  have h8 (q : Pattern) (ha : d194490 q = 1) (hb : d202307 q = 1) : d207590 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d194490, d207590, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d194490, d207590, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d194491 q = 1) (hb : d202307 q = 1) : d207591 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d194491, d207591, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d194491, d207591, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d194492 q = 1) (hb : d202307 q = 1) : d207592 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d194492, d207592, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d194492, d207592, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d194527 q = 1) (hb : d202307 q = 1) : d207623 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d194527, d207623, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d194527, d207623, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48618 q ha hb
  have h12 (q : Pattern) (ha : d194528 q = 1) (hb : d202307 q = 1) : d207624 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d194528, d207624, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d194528, d207624, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d194529 q = 1) (hb : d202307 q = 1) : d207625 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d194529, d207625, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d194529, d207625, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d194530 q = 1) (hb : d202307 q = 1) : d207626 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d194530, d207626, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d194530, d207626, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d194531 q = 1) (hb : d202307 q = 1) : d207627 q = 1 := by
    cases bit : q 10250 with
    | false =>
      simp only [d194531, d207627, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d194531, d207627, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d194532 q = 1) (hb : d202307 q = 1) : d207628 q = 1 := by
    cases bit : q 260 with
    | false =>
      simp only [d194532, d207628, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d194532, d207628, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  exact h16 p ha hb
theorem andIntro48620 (p : Pattern) (ha : d194538 p = 1) (hb : d202307 p = 1) : d207634 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d202307 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d194533 q = 1) (hb : d202307 q = 1) : d207629 q = 1 := by
    cases bit : q 259 with
    | false =>
      simp only [d194533, d207629, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48619 q ha hb
    | true =>
      simp only [d194533, d207629, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d194534 q = 1) (hb : d202307 q = 1) : d207630 q = 1 := by
    cases bit : q 258 with
    | false =>
      simp only [d194534, d207630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d194534, d207630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d194535 q = 1) (hb : d202307 q = 1) : d207631 q = 1 := by
    cases bit : q 257 with
    | false =>
      simp only [d194535, d207631, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d194535, d207631, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d194536 q = 1) (hb : d202307 q = 1) : d207632 q = 1 := by
    cases bit : q 256 with
    | false =>
      simp only [d194536, d207632, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d194536, d207632, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d194537 q = 1) (hb : d202307 q = 1) : d207633 q = 1 := by
    cases bit : q 255 with
    | false =>
      simp only [d194537, d207633, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d194537, d207633, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d194538 q = 1) (hb : d202307 q = 1) : d207634 q = 1 := by
    cases bit : q 254 with
    | false =>
      simp only [d194538, d207634, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d194538, d207634, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro48621 (p : Pattern) (ha : d194544 p = 1) (hb : d202307 p = 1) : d207640 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d202307 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d194539 q = 1) (hb : d202307 q = 1) : d207635 q = 1 := by
    cases bit : q 253 with
    | false =>
      simp only [d194539, d207635, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48620 q ha hb
    | true =>
      simp only [d194539, d207635, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d194540 q = 1) (hb : d202307 q = 1) : d207636 q = 1 := by
    cases bit : q 252 with
    | false =>
      simp only [d194540, d207636, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d194540, d207636, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d194541 q = 1) (hb : d202307 q = 1) : d207637 q = 1 := by
    cases bit : q 251 with
    | false =>
      simp only [d194541, d207637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d194541, d207637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d194542 q = 1) (hb : d202307 q = 1) : d207638 q = 1 := by
    cases bit : q 250 with
    | false =>
      simp only [d194542, d207638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d194542, d207638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d194543 q = 1) (hb : d202307 q = 1) : d207639 q = 1 := by
    cases bit : q 249 with
    | false =>
      simp only [d194543, d207639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d194543, d207639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d194544 q = 1) (hb : d202307 q = 1) : d207640 q = 1 := by
    cases bit : q 245 with
    | false =>
      simp only [d194544, d207640, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d194544, d207640, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro48622 (p : Pattern) (ha : d194550 p = 1) (hb : d202307 p = 1) : d207646 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d202307 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d194545 q = 1) (hb : d202307 q = 1) : d207641 q = 1 := by
    cases bit : q 200 with
    | false =>
      simp only [d194545, d207641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48621 q ha hb
    | true =>
      simp only [d194545, d207641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d194546 q = 1) (hb : d202307 q = 1) : d207642 q = 1 := by
    cases bit : q 199 with
    | false =>
      simp only [d194546, d207642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d194546, d207642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d194547 q = 1) (hb : d202307 q = 1) : d207643 q = 1 := by
    cases bit : q 186 with
    | false =>
      simp only [d194547, d207643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d194547, d207643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d194548 q = 1) (hb : d202307 q = 1) : d207644 q = 1 := by
    cases bit : q 185 with
    | false =>
      simp only [d194548, d207644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d194548, d207644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d194549 q = 1) (hb : d202307 q = 1) : d207645 q = 1 := by
    cases bit : q 184 with
    | false =>
      simp only [d194549, d207645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d194549, d207645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d194550 q = 1) (hb : d202307 q = 1) : d207646 q = 1 := by
    cases bit : q 181 with
    | false =>
      simp only [d194550, d207646, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d194550, d207646, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro48623 (p : Pattern) (ha : d194556 p = 1) (hb : d202307 p = 1) : d207652 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d202307 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d194551 q = 1) (hb : d202307 q = 1) : d207647 q = 1 := by
    cases bit : q 177 with
    | false =>
      simp only [d194551, d207647, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48622 q ha hb
    | true =>
      simp only [d194551, d207647, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d194552 q = 1) (hb : d202307 q = 1) : d207648 q = 1 := by
    cases bit : q 164 with
    | false =>
      simp only [d194552, d207648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d194552, d207648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d194553 q = 1) (hb : d202307 q = 1) : d207649 q = 1 := by
    cases bit : q 156 with
    | false =>
      simp only [d194553, d207649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d194553, d207649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d194554 q = 1) (hb : d202307 q = 1) : d207650 q = 1 := by
    cases bit : q 155 with
    | false =>
      simp only [d194554, d207650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d194554, d207650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d194555 q = 1) (hb : d202307 q = 1) : d207651 q = 1 := by
    cases bit : q 134 with
    | false =>
      simp only [d194555, d207651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d194555, d207651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d194556 q = 1) (hb : d202307 q = 1) : d207652 q = 1 := by
    cases bit : q 133 with
    | false =>
      simp only [d194556, d207652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d194556, d207652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro48624 (p : Pattern) (ha : d194562 p = 1) (hb : d202307 p = 1) : d207658 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d202307 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d194557 q = 1) (hb : d202307 q = 1) : d207653 q = 1 := by
    cases bit : q 120 with
    | false =>
      simp only [d194557, d207653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48623 q ha hb
    | true =>
      simp only [d194557, d207653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d194558 q = 1) (hb : d202307 q = 1) : d207654 q = 1 := by
    cases bit : q 118 with
    | false =>
      simp only [d194558, d207654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d194558, d207654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d194559 q = 1) (hb : d202307 q = 1) : d207655 q = 1 := by
    cases bit : q 114 with
    | false =>
      simp only [d194559, d207655, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d194559, d207655, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d194560 q = 1) (hb : d202307 q = 1) : d207656 q = 1 := by
    cases bit : q 111 with
    | false =>
      simp only [d194560, d207656, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d194560, d207656, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d194561 q = 1) (hb : d202307 q = 1) : d207657 q = 1 := by
    cases bit : q 98 with
    | false =>
      simp only [d194561, d207657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d194561, d207657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d194562 q = 1) (hb : d202307 q = 1) : d207658 q = 1 := by
    cases bit : q 97 with
    | false =>
      simp only [d194562, d207658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d194562, d207658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro48625 (p : Pattern) (ha : d194568 p = 1) (hb : d202307 p = 1) : d207664 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d202307 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d194563 q = 1) (hb : d202307 q = 1) : d207659 q = 1 := by
    cases bit : q 94 with
    | false =>
      simp only [d194563, d207659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48624 q ha hb
    | true =>
      simp only [d194563, d207659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d194564 q = 1) (hb : d202307 q = 1) : d207660 q = 1 := by
    cases bit : q 76 with
    | false =>
      simp only [d194564, d207660, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d194564, d207660, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d194565 q = 1) (hb : d202307 q = 1) : d207661 q = 1 := by
    cases bit : q 67 with
    | false =>
      simp only [d194565, d207661, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d194565, d207661, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d194566 q = 1) (hb : d202307 q = 1) : d207662 q = 1 := by
    cases bit : q 52 with
    | false =>
      simp only [d194566, d207662, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d194566, d207662, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d194567 q = 1) (hb : d202307 q = 1) : d207663 q = 1 := by
    cases bit : q 47 with
    | false =>
      simp only [d194567, d207663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d194567, d207663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d194568 q = 1) (hb : d202307 q = 1) : d207664 q = 1 := by
    cases bit : q 46 with
    | false =>
      simp only [d194568, d207664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d194568, d207664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro48626 (p : Pattern) (ha : d194574 p = 1) (hb : d202307 p = 1) : d207670 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d202307 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d194569 q = 1) (hb : d202307 q = 1) : d207665 q = 1 := by
    cases bit : q 45 with
    | false =>
      simp only [d194569, d207665, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48625 q ha hb
    | true =>
      simp only [d194569, d207665, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d194570 q = 1) (hb : d202307 q = 1) : d207666 q = 1 := by
    cases bit : q 30 with
    | false =>
      simp only [d194570, d207666, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d194570, d207666, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d194571 q = 1) (hb : d202307 q = 1) : d207667 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d194571, d207667, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d194571, d207667, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d194572 q = 1) (hb : d202307 q = 1) : d207668 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d194572, d207668, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d194572, d207668, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d194573 q = 1) (hb : d202307 q = 1) : d207669 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d194573, d207669, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d194573, d207669, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d194574 q = 1) (hb : d202307 q = 1) : d207670 q = 1 := by
    cases bit : q 25 with
    | false =>
      simp only [d194574, d207670, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d194574, d207670, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro48627 (p : Pattern) (ha : d204501 p = 1) (hb : d205975 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d204466 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d204472 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d204496 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d204388 q = 1) (hb : d205913 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d204388, d205913, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48278 q ha hb
    | true =>
      simp only [d204388, d205913, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d204497 q = 1) (hb : d205971 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d204497, d205971, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d204497, d205971, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d204389 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d204498 q = 1) (hb : d205972 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d204498, d205972, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d204498, d205972, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d204499 q = 1) (hb : d205973 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d204499, d205973, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d204499, d205973, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d204500 q = 1) (hb : d205974 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d204500, d205974, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d204500, d205974, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d204501 q = 1) (hb : d205975 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d204501, d205975, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d204501, d205975, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro48628 (p : Pattern) (ha : d204517 p = 1) (hb : d205982 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d204466 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d204472 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d204496 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d204388 q = 1) (hb : d205913 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d204388, d205913, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48278 q ha hb
    | true =>
      simp only [d204388, d205913, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d204497 q = 1) (hb : d205971 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d204497, d205971, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d204497, d205971, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d204389 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d204498 q = 1) (hb : d205972 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d204498, d205972, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d204498, d205972, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d204499 q = 1) (hb : d205973 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d204499, d205973, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d204499, d205973, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d204500 q = 1) (hb : d205974 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d204500, d205974, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d204500, d205974, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d204506 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d204510 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d204512 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d204395 q = 1) (hb : d205920 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d204395, d205920, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48280 q ha hb
    | true =>
      simp only [d204395, d205920, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h14 (q : Pattern) (ha : d204513 q = 1) (hb : d205978 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d204513, d205978, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
    | true =>
      simp only [d204513, d205978, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d0 q = 1) (hb : d204396 q = 1) : d0 q = 1 := by
    exact ha
  have h16 (q : Pattern) (ha : d204514 q = 1) (hb : d205979 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d204514, d205979, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d204514, d205979, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q hb ha
  have h17 (q : Pattern) (ha : d204515 q = 1) (hb : d205980 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d204515, d205980, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
    | true =>
      simp only [d204515, d205980, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d204516 q = 1) (hb : d205981 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d204516, d205981, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
    | true =>
      simp only [d204516, d205981, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d204517 q = 1) (hb : d205982 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d204517, d205982, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d204517, d205982, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro48629 (p : Pattern) (ha : d204526 p = 1) (hb : d206194 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d204512 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d204395 q = 1) (hb : d205920 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d204395, d205920, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48280 q ha hb
    | true =>
      simp only [d204395, d205920, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d204513 q = 1) (hb : d205978 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d204513, d205978, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d204513, d205978, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d204396 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d204514 q = 1) (hb : d205979 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d204514, d205979, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d204514, d205979, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d204524 q = 1) (hb : d205980 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d204524, d205980, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d204524, d205980, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d204525 q = 1) (hb : d205981 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d204525, d205981, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d204525, d205981, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d204526 q = 1) (hb : d206194 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d204526, d206194, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d204526, d206194, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro48630 (p : Pattern) (ha : d204555 p = 1) (hb : d206240 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d204550 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d204429 q = 1) (hb : d205954 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d204429, d205954, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48285 q ha hb
    | true =>
      simp only [d204429, d205954, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d204551 q = 1) (hb : d206236 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d204551, d206236, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d204551, d206236, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d204430 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d204552 q = 1) (hb : d206237 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d204552, d206237, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d204552, d206237, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d204553 q = 1) (hb : d206238 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d204553, d206238, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d204553, d206238, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d204554 q = 1) (hb : d206239 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d204554, d206239, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d204554, d206239, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d204555 q = 1) (hb : d206240 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d204555, d206240, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d204555, d206240, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro48631 (p : Pattern) (ha : d204561 p = 1) (hb : d207465 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d204460 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d204518 q = 1) (hb : d205983 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d204518, d205983, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48627 q ha hb
    | true =>
      simp only [d204518, d205983, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48628 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d204520 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d204521 q = 1) (hb : d205984 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d204521, d205984, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d204521, d205984, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d204522 q = 1) (hb : d207455 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d204522, d207455, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d204522, d207455, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d204523 q = 1) (hb : d207456 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d204523, d207456, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d204523, d207456, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d204527 q = 1) (hb : d206195 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d204527, d206195, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d204527, d206195, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48629 q ha hb
  have h8 (q : Pattern) (ha : d204528 q = 1) (hb : d207457 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d204528, d207457, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d204528, d207457, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h9 (q : Pattern) (ha : d204529 q = 1) (hb : d207458 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d204529, d207458, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d204529, d207458, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h10 (q : Pattern) (ha : d204530 q = 1) (hb : d207459 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d204530, d207459, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d204530, d207459, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h11 (q : Pattern) (ha : d204531 q = 1) (hb : d207460 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d204531, d207460, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d204531, d207460, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d204556 q = 1) (hb : d206241 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d204556, d206241, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d204556, d206241, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48630 q ha hb
  have h13 (q : Pattern) (ha : d204557 q = 1) (hb : d207461 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d204557, d207461, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d204557, d207461, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h14 (q : Pattern) (ha : d204558 q = 1) (hb : d207462 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d204558, d207462, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d204558, d207462, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h15 (q : Pattern) (ha : d204559 q = 1) (hb : d207463 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d204559, d207463, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d204559, d207463, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h16 (q : Pattern) (ha : d204560 q = 1) (hb : d207464 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d204560, d207464, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d204560, d207464, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h17 (q : Pattern) (ha : d204561 q = 1) (hb : d207465 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d204561, d207465, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d204561, d207465, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  exact h17 p ha hb
theorem andIntro48632 (p : Pattern) (ha : d204567 p = 1) (hb : d207471 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d204445 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d204562 q = 1) (hb : d207466 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d204562, d207466, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d204562, d207466, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48631 q ha hb
  have h3 (q : Pattern) (ha : d204563 q = 1) (hb : d207467 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d204563, d207467, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d204563, d207467, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d204564 q = 1) (hb : d207468 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d204564, d207468, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d204564, d207468, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d204565 q = 1) (hb : d207469 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d204565, d207469, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d204565, d207469, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d204566 q = 1) (hb : d207470 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d204566, d207470, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d204566, d207470, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d204567 q = 1) (hb : d207471 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d204567, d207471, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d204567, d207471, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro48633 (p : Pattern) (ha : d204637 p = 1) (hb : d206096 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d204588 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d204594 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d204626 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d204496 q = 1) (hb : d206020 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d204496, d206020, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48296 q ha hb
    | true =>
      simp only [d204496, d206020, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48278 q ha hb
  have h5 (q : Pattern) (ha : d204627 q = 1) (hb : d206092 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d204627, d206092, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d204627, d206092, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d204633 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d204634 q = 1) (hb : d206093 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d204634, d206093, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d204634, d206093, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d204635 q = 1) (hb : d206094 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d204635, d206094, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d204635, d206094, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d204636 q = 1) (hb : d206095 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d204636, d206095, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d204636, d206095, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d204637 q = 1) (hb : d206096 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d204637, d206096, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d204637, d206096, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro48634 (p : Pattern) (ha : d204656 p = 1) (hb : d206103 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d204588 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d204594 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d204626 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d204496 q = 1) (hb : d206020 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d204496, d206020, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48296 q ha hb
    | true =>
      simp only [d204496, d206020, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48278 q ha hb
  have h4 (q : Pattern) (ha : d204627 q = 1) (hb : d206092 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d204627, d206092, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d204627, d206092, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d204633 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d204634 q = 1) (hb : d206093 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d204634, d206093, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d204634, d206093, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d204635 q = 1) (hb : d206094 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d204635, d206094, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d204635, d206094, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d204636 q = 1) (hb : d206095 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d204636, d206095, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d204636, d206095, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d204642 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d204646 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d204648 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d204512 q = 1) (hb : d206036 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d204512, d206036, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48300 q ha hb
    | true =>
      simp only [d204512, d206036, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48280 q ha hb
  have h13 (q : Pattern) (ha : d204649 q = 1) (hb : d206099 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d204649, d206099, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
    | true =>
      simp only [d204649, d206099, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d204652 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d204653 q = 1) (hb : d206100 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d204653, d206100, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d204653, d206100, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d204654 q = 1) (hb : d206101 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d204654, d206101, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
    | true =>
      simp only [d204654, d206101, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d204655 q = 1) (hb : d206102 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d204655, d206102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
    | true =>
      simp only [d204655, d206102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d204656 q = 1) (hb : d206103 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d204656, d206103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d204656, d206103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro48635 (p : Pattern) (ha : d204665 p = 1) (hb : d207474 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d204648 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d204512 q = 1) (hb : d206036 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d204512, d206036, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48300 q ha hb
    | true =>
      simp only [d204512, d206036, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48280 q ha hb
  have h3 (q : Pattern) (ha : d204649 q = 1) (hb : d206099 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d204649, d206099, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d204649, d206099, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d204652 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d204653 q = 1) (hb : d206100 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d204653, d206100, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d204653, d206100, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d204663 q = 1) (hb : d206101 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d204663, d206101, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d204663, d206101, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d204664 q = 1) (hb : d206102 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d204664, d206102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d204664, d206102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d204665 q = 1) (hb : d207474 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d204665, d207474, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d204665, d207474, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro48636 (p : Pattern) (ha : d204707 p = 1) (hb : d207484 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d204696 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d204550 q = 1) (hb : d206074 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d204550, d206074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48306 q ha hb
    | true =>
      simp only [d204550, d206074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48285 q ha hb
  have h3 (q : Pattern) (ha : d204697 q = 1) (hb : d207480 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d204697, d207480, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d204697, d207480, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d204703 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d204704 q = 1) (hb : d207481 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d204704, d207481, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d204704, d207481, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d204705 q = 1) (hb : d207482 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d204705, d207482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d204705, d207482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d204706 q = 1) (hb : d207483 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d204706, d207483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d204706, d207483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d204707 q = 1) (hb : d207484 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d204707, d207484, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d204707, d207484, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro48637 (p : Pattern) (ha : d204719 p = 1) (hb : d207490 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d204582 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d204657 q = 1) (hb : d206104 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d204657, d206104, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48633 q ha hb
    | true =>
      simp only [d204657, d206104, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48634 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d204659 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d204660 q = 1) (hb : d206105 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d204660, d206105, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d204660, d206105, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d204661 q = 1) (hb : d207472 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d204661, d207472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d204661, d207472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d204662 q = 1) (hb : d207473 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d204662, d207473, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d204662, d207473, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d204666 q = 1) (hb : d207475 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d204666, d207475, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d204666, d207475, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48635 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d204668 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d204669 q = 1) (hb : d207476 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d204669, d207476, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d204669, d207476, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d204670 q = 1) (hb : d207477 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d204670, d207477, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d204670, d207477, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h11 (q : Pattern) (ha : d204671 q = 1) (hb : d207478 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d204671, d207478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d204671, d207478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h12 (q : Pattern) (ha : d204672 q = 1) (hb : d207479 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d204672, d207479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d204672, d207479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d204708 q = 1) (hb : d207485 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d204708, d207485, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d204708, d207485, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48636 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d204714 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d204715 q = 1) (hb : d207486 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d204715, d207486, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d204715, d207486, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d204716 q = 1) (hb : d207487 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d204716, d207487, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d204716, d207487, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h17 (q : Pattern) (ha : d204717 q = 1) (hb : d207488 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d204717, d207488, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d204717, d207488, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h18 (q : Pattern) (ha : d204718 q = 1) (hb : d207489 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d204718, d207489, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d204718, d207489, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h19 (q : Pattern) (ha : d204719 q = 1) (hb : d207490 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d204719, d207490, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d204719, d207490, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro48638 (p : Pattern) (ha : d204725 p = 1) (hb : d207496 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d204720 q = 1) (hb : d207491 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d204720, d207491, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d204720, d207491, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48637 q ha hb
  have h2 (q : Pattern) (ha : d204721 q = 1) (hb : d207492 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d204721, d207492, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d204721, d207492, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d204722 q = 1) (hb : d207493 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d204722, d207493, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d204722, d207493, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d204723 q = 1) (hb : d207494 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d204723, d207494, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d204723, d207494, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d204724 q = 1) (hb : d207495 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d204724, d207495, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d204724, d207495, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d204725 q = 1) (hb : d207496 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d204725, d207496, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d204725, d207496, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro48639 (p : Pattern) (ha : d204828 p = 1) (hb : d206276 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d204770 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d204779 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d204817 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d204744 q = 1) (hb : d206271 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d204744, d206271, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48341 q ha hb
    | true =>
      simp only [d204744, d206271, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48342 q ha hb
  have h5 (q : Pattern) (ha : d204818 q = 1) (hb : d206272 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d204818, d206272, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d204818, d206272, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d204824 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d204825 q = 1) (hb : d206273 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d204825, d206273, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d204825, d206273, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d204826 q = 1) (hb : d206274 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d204826, d206274, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d204826, d206274, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d204827 q = 1) (hb : d206275 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d204827, d206275, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d204827, d206275, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d204828 q = 1) (hb : d206276 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d204828, d206276, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d204828, d206276, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro48640 (p : Pattern) (ha : d204849 p = 1) (hb : d206286 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d204770 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d204779 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d204817 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d204744 q = 1) (hb : d206271 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d204744, d206271, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48341 q ha hb
    | true =>
      simp only [d204744, d206271, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48342 q ha hb
  have h4 (q : Pattern) (ha : d204818 q = 1) (hb : d206272 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d204818, d206272, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d204818, d206272, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d204824 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d204825 q = 1) (hb : d206273 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d204825, d206273, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d204825, d206273, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d204826 q = 1) (hb : d206274 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d204826, d206274, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d204826, d206274, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d204827 q = 1) (hb : d206275 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d204827, d206275, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d204827, d206275, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d204834 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d204839 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d204841 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d204754 q = 1) (hb : d206281 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d204754, d206281, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48344 q ha hb
    | true =>
      simp only [d204754, d206281, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48345 q ha hb
  have h13 (q : Pattern) (ha : d204842 q = 1) (hb : d206282 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d204842, d206282, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
    | true =>
      simp only [d204842, d206282, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d204845 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d204846 q = 1) (hb : d206283 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d204846, d206283, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d204846, d206283, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d204847 q = 1) (hb : d206284 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d204847, d206284, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
    | true =>
      simp only [d204847, d206284, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d204848 q = 1) (hb : d206285 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d204848, d206285, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
    | true =>
      simp only [d204848, d206285, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d204849 q = 1) (hb : d206286 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d204849, d206286, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d204849, d206286, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro48641 (p : Pattern) (ha : d204869 p = 1) (hb : d207500 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d204841 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d204754 q = 1) (hb : d206281 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d204754, d206281, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48344 q ha hb
    | true =>
      simp only [d204754, d206281, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48345 q ha hb
  have h3 (q : Pattern) (ha : d204842 q = 1) (hb : d206282 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d204842, d206282, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d204842, d206282, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d204845 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d204846 q = 1) (hb : d206283 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d204846, d206283, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d204846, d206283, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d204867 q = 1) (hb : d206284 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d204867, d206284, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d204867, d206284, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d204868 q = 1) (hb : d206285 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d204868, d206285, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d204868, d206285, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d204869 q = 1) (hb : d207500 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d204869, d207500, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d204869, d207500, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro48642 (p : Pattern) (ha : d204933 p = 1) (hb : d207511 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d204917 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d204922 q = 1) (hb : d207506 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d204922, d207506, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48379 q ha hb
    | true =>
      simp only [d204922, d207506, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48382 q ha hb
  have h3 (q : Pattern) (ha : d204923 q = 1) (hb : d207507 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d204923, d207507, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d204923, d207507, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d204929 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d204930 q = 1) (hb : d207508 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d204930, d207508, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d204930, d207508, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d204931 q = 1) (hb : d207509 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d204931, d207509, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d204931, d207509, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d204932 q = 1) (hb : d207510 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d204932, d207510, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d204932, d207510, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d204933 q = 1) (hb : d207511 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d204933, d207511, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d204933, d207511, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro48643 (p : Pattern) (ha : d204946 p = 1) (hb : d207517 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d204762 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d204850 q = 1) (hb : d206287 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d204850, d206287, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48639 q ha hb
    | true =>
      simp only [d204850, d206287, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48640 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d204863 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d204864 q = 1) (hb : d206288 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d204864, d206288, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d204864, d206288, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d204865 q = 1) (hb : d207498 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d204865, d207498, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d204865, d207498, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d204866 q = 1) (hb : d207499 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d204866, d207499, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d204866, d207499, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d204870 q = 1) (hb : d207501 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d204870, d207501, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d204870, d207501, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48641 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d204872 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d204873 q = 1) (hb : d207502 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d204873, d207502, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d204873, d207502, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d204874 q = 1) (hb : d207503 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d204874, d207503, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d204874, d207503, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h11 (q : Pattern) (ha : d204875 q = 1) (hb : d207504 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d204875, d207504, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d204875, d207504, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h12 (q : Pattern) (ha : d204876 q = 1) (hb : d207505 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d204876, d207505, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d204876, d207505, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d204934 q = 1) (hb : d207512 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d204934, d207512, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d204934, d207512, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48642 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d204941 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d204942 q = 1) (hb : d207513 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d204942, d207513, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d204942, d207513, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d204943 q = 1) (hb : d207514 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d204943, d207514, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d204943, d207514, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h17 (q : Pattern) (ha : d204944 q = 1) (hb : d207515 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d204944, d207515, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d204944, d207515, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h18 (q : Pattern) (ha : d204945 q = 1) (hb : d207516 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d204945, d207516, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d204945, d207516, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h19 (q : Pattern) (ha : d204946 q = 1) (hb : d207517 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d204946, d207517, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d204946, d207517, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro48644 (p : Pattern) (ha : d204952 p = 1) (hb : d207523 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d204947 q = 1) (hb : d207518 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d204947, d207518, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d204947, d207518, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48643 q ha hb
  have h2 (q : Pattern) (ha : d204948 q = 1) (hb : d207519 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d204948, d207519, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d204948, d207519, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d204949 q = 1) (hb : d207520 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d204949, d207520, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d204949, d207520, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d204950 q = 1) (hb : d207521 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d204950, d207521, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d204950, d207521, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d204951 q = 1) (hb : d207522 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d204951, d207522, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d204951, d207522, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d204952 q = 1) (hb : d207523 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d204952, d207523, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d204952, d207523, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro48645 (p : Pattern) (ha : d205102 p = 1) (hb : d206550 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d205044 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d205053 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d205091 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d205018 q = 1) (hb : d206545 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d205018, d206545, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48399 q ha hb
    | true =>
      simp only [d205018, d206545, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48400 q ha hb
  have h5 (q : Pattern) (ha : d205092 q = 1) (hb : d206546 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d205092, d206546, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d205092, d206546, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d205098 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d205099 q = 1) (hb : d206547 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d205099, d206547, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d205099, d206547, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d205100 q = 1) (hb : d206548 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d205100, d206548, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d205100, d206548, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d205101 q = 1) (hb : d206549 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d205101, d206549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d205101, d206549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d205102 q = 1) (hb : d206550 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d205102, d206550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d205102, d206550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro48646 (p : Pattern) (ha : d205123 p = 1) (hb : d206560 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d205044 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d205053 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d205091 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d205018 q = 1) (hb : d206545 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d205018, d206545, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48399 q ha hb
    | true =>
      simp only [d205018, d206545, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48400 q ha hb
  have h4 (q : Pattern) (ha : d205092 q = 1) (hb : d206546 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d205092, d206546, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d205092, d206546, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d205098 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d205099 q = 1) (hb : d206547 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d205099, d206547, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d205099, d206547, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d205100 q = 1) (hb : d206548 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d205100, d206548, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d205100, d206548, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d205101 q = 1) (hb : d206549 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d205101, d206549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d205101, d206549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d205108 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d205113 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d205115 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d205028 q = 1) (hb : d206555 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d205028, d206555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48402 q ha hb
    | true =>
      simp only [d205028, d206555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48403 q ha hb
  have h13 (q : Pattern) (ha : d205116 q = 1) (hb : d206556 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d205116, d206556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
    | true =>
      simp only [d205116, d206556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d205119 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d205120 q = 1) (hb : d206557 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d205120, d206557, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d205120, d206557, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d205121 q = 1) (hb : d206558 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d205121, d206558, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
    | true =>
      simp only [d205121, d206558, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d205122 q = 1) (hb : d206559 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d205122, d206559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
    | true =>
      simp only [d205122, d206559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d205123 q = 1) (hb : d206560 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d205123, d206560, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d205123, d206560, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro48647 (p : Pattern) (ha : d205143 p = 1) (hb : d207528 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d205115 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d205028 q = 1) (hb : d206555 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d205028, d206555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48402 q ha hb
    | true =>
      simp only [d205028, d206555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48403 q ha hb
  have h3 (q : Pattern) (ha : d205116 q = 1) (hb : d206556 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d205116, d206556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d205116, d206556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d205119 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d205120 q = 1) (hb : d206557 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d205120, d206557, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d205120, d206557, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d205141 q = 1) (hb : d206558 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d205141, d206558, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d205141, d206558, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d205142 q = 1) (hb : d206559 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d205142, d206559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d205142, d206559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d205143 q = 1) (hb : d207528 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d205143, d207528, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d205143, d207528, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro48648 (p : Pattern) (ha : d205220 p = 1) (hb : d207537 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d205207 q = 1) (hb : d206771 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d205207, d206771, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48444 q ha hb
    | true =>
      simp only [d205207, d206771, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d205208 q = 1) (hb : d206772 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d205208, d206772, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d205208, d206772, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d205215 q = 1) (hb : d206761 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d205215, d206761, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48442 q ha hb
    | true =>
      simp only [d205215, d206761, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d205216 q = 1) (hb : d206762 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d205216, d206762, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d205216, d206762, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d205217 q = 1) (hb : d207534 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d205217, d207534, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d205217, d207534, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d205218 q = 1) (hb : d207535 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d205218, d207535, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d205218, d207535, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d205219 q = 1) (hb : d207536 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d205219, d207536, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d205219, d207536, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d205220 q = 1) (hb : d207537 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d205220, d207537, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d205220, d207537, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro48649 (p : Pattern) (ha : d205237 p = 1) (hb : d207543 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d205221 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d205226 q = 1) (hb : d207538 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d205226, d207538, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48648 q ha hb
    | true =>
      simp only [d205226, d207538, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48447 q ha hb
  have h3 (q : Pattern) (ha : d205227 q = 1) (hb : d207539 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d205227, d207539, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d205227, d207539, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d205233 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d205234 q = 1) (hb : d207540 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d205234, d207540, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d205234, d207540, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d205235 q = 1) (hb : d207541 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d205235, d207541, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d205235, d207541, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d205236 q = 1) (hb : d207542 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d205236, d207542, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d205236, d207542, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d205237 q = 1) (hb : d207543 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d205237, d207543, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d205237, d207543, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro48650 (p : Pattern) (ha : d205250 p = 1) (hb : d207549 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d205036 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d205124 q = 1) (hb : d206561 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d205124, d206561, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48645 q ha hb
    | true =>
      simp only [d205124, d206561, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48646 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d205137 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d205138 q = 1) (hb : d206562 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d205138, d206562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d205138, d206562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d205139 q = 1) (hb : d207526 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d205139, d207526, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d205139, d207526, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d205140 q = 1) (hb : d207527 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d205140, d207527, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d205140, d207527, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d205144 q = 1) (hb : d207529 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d205144, d207529, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d205144, d207529, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48647 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d205146 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d205147 q = 1) (hb : d207530 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d205147, d207530, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d205147, d207530, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d205148 q = 1) (hb : d207531 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d205148, d207531, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d205148, d207531, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h11 (q : Pattern) (ha : d205149 q = 1) (hb : d207532 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d205149, d207532, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d205149, d207532, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h12 (q : Pattern) (ha : d205150 q = 1) (hb : d207533 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d205150, d207533, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d205150, d207533, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d205238 q = 1) (hb : d207544 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d205238, d207544, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d205238, d207544, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48649 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d205245 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d205246 q = 1) (hb : d207545 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d205246, d207545, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d205246, d207545, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d205247 q = 1) (hb : d207546 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d205247, d207546, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d205247, d207546, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h17 (q : Pattern) (ha : d205248 q = 1) (hb : d207547 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d205248, d207547, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d205248, d207547, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h18 (q : Pattern) (ha : d205249 q = 1) (hb : d207548 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d205249, d207548, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d205249, d207548, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h19 (q : Pattern) (ha : d205250 q = 1) (hb : d207549 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d205250, d207549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d205250, d207549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro48651 (p : Pattern) (ha : d205256 p = 1) (hb : d207555 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d205251 q = 1) (hb : d207550 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d205251, d207550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d205251, d207550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48650 q ha hb
  have h2 (q : Pattern) (ha : d205252 q = 1) (hb : d207551 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d205252, d207551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d205252, d207551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d205253 q = 1) (hb : d207552 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d205253, d207552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d205253, d207552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d205254 q = 1) (hb : d207553 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d205254, d207553, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d205254, d207553, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d205255 q = 1) (hb : d207554 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d205255, d207554, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d205255, d207554, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d205256 q = 1) (hb : d207555 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d205256, d207555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d205256, d207555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro48652 (p : Pattern) (ha : d205407 p = 1) (hb : d206878 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d205355 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d205364 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d205396 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d205329 q = 1) (hb : d206873 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d205329, d206873, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48469 q ha hb
    | true =>
      simp only [d205329, d206873, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48470 q ha hb
  have h5 (q : Pattern) (ha : d205397 q = 1) (hb : d206874 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d205397, d206874, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d205397, d206874, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d205403 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d205404 q = 1) (hb : d206875 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d205404, d206875, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d205404, d206875, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d205405 q = 1) (hb : d206876 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d205405, d206876, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d205405, d206876, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d205406 q = 1) (hb : d206877 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d205406, d206877, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d205406, d206877, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d205407 q = 1) (hb : d206878 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d205407, d206878, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d205407, d206878, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro48653 (p : Pattern) (ha : d205428 p = 1) (hb : d206888 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d205355 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d205364 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d205396 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d205329 q = 1) (hb : d206873 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d205329, d206873, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48469 q ha hb
    | true =>
      simp only [d205329, d206873, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48470 q ha hb
  have h4 (q : Pattern) (ha : d205397 q = 1) (hb : d206874 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d205397, d206874, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d205397, d206874, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d205403 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d205404 q = 1) (hb : d206875 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d205404, d206875, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d205404, d206875, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d205405 q = 1) (hb : d206876 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d205405, d206876, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d205405, d206876, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d205406 q = 1) (hb : d206877 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d205406, d206877, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d205406, d206877, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d205413 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d205418 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d205420 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d205339 q = 1) (hb : d206883 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d205339, d206883, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48472 q ha hb
    | true =>
      simp only [d205339, d206883, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48473 q ha hb
  have h13 (q : Pattern) (ha : d205421 q = 1) (hb : d206884 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d205421, d206884, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
    | true =>
      simp only [d205421, d206884, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d205424 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d205425 q = 1) (hb : d206885 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d205425, d206885, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d205425, d206885, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d205426 q = 1) (hb : d206886 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d205426, d206886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
    | true =>
      simp only [d205426, d206886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d205427 q = 1) (hb : d206887 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d205427, d206887, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
    | true =>
      simp only [d205427, d206887, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d205428 q = 1) (hb : d206888 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d205428, d206888, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d205428, d206888, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro48654 (p : Pattern) (ha : d205448 p = 1) (hb : d207561 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d205420 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d205339 q = 1) (hb : d206883 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d205339, d206883, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48472 q ha hb
    | true =>
      simp only [d205339, d206883, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48473 q ha hb
  have h3 (q : Pattern) (ha : d205421 q = 1) (hb : d206884 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d205421, d206884, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d205421, d206884, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d205424 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d205425 q = 1) (hb : d206885 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d205425, d206885, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d205425, d206885, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d205446 q = 1) (hb : d206886 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d205446, d206886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d205446, d206886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d205447 q = 1) (hb : d206887 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d205447, d206887, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d205447, d206887, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d205448 q = 1) (hb : d207561 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d205448, d207561, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d205448, d207561, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro48655 (p : Pattern) (ha : d205525 p = 1) (hb : d207570 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d205512 q = 1) (hb : d207083 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d205512, d207083, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48512 q ha hb
    | true =>
      simp only [d205512, d207083, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d205513 q = 1) (hb : d207084 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d205513, d207084, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d205513, d207084, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d205520 q = 1) (hb : d207073 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d205520, d207073, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48510 q ha hb
    | true =>
      simp only [d205520, d207073, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d205521 q = 1) (hb : d207074 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d205521, d207074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d205521, d207074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d205522 q = 1) (hb : d207567 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d205522, d207567, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d205522, d207567, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d205523 q = 1) (hb : d207568 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d205523, d207568, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d205523, d207568, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d205524 q = 1) (hb : d207569 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d205524, d207569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d205524, d207569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d205525 q = 1) (hb : d207570 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d205525, d207570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d205525, d207570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro48656 (p : Pattern) (ha : d205542 p = 1) (hb : d207576 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d205526 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d205531 q = 1) (hb : d207571 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d205531, d207571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48655 q ha hb
    | true =>
      simp only [d205531, d207571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48515 q ha hb
  have h3 (q : Pattern) (ha : d205532 q = 1) (hb : d207572 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d205532, d207572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d205532, d207572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d205538 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d205539 q = 1) (hb : d207573 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d205539, d207573, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d205539, d207573, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d205540 q = 1) (hb : d207574 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d205540, d207574, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d205540, d207574, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d205541 q = 1) (hb : d207575 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d205541, d207575, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d205541, d207575, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d205542 q = 1) (hb : d207576 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d205542, d207576, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d205542, d207576, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro48657 (p : Pattern) (ha : d205555 p = 1) (hb : d207582 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d205347 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d205429 q = 1) (hb : d206889 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d205429, d206889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48652 q ha hb
    | true =>
      simp only [d205429, d206889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48653 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d205442 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d205443 q = 1) (hb : d206890 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d205443, d206890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d205443, d206890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d205444 q = 1) (hb : d207559 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d205444, d207559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d205444, d207559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d205445 q = 1) (hb : d207560 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d205445, d207560, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d205445, d207560, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d205449 q = 1) (hb : d207562 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d205449, d207562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d205449, d207562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48654 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d205451 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d205452 q = 1) (hb : d207563 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d205452, d207563, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d205452, d207563, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d205453 q = 1) (hb : d207564 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d205453, d207564, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d205453, d207564, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h11 (q : Pattern) (ha : d205454 q = 1) (hb : d207565 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d205454, d207565, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d205454, d207565, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h12 (q : Pattern) (ha : d205455 q = 1) (hb : d207566 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d205455, d207566, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d205455, d207566, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d205543 q = 1) (hb : d207577 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d205543, d207577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d205543, d207577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48656 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d205550 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d205551 q = 1) (hb : d207578 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d205551, d207578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d205551, d207578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d205552 q = 1) (hb : d207579 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d205552, d207579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d205552, d207579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h17 (q : Pattern) (ha : d205553 q = 1) (hb : d207580 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d205553, d207580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d205553, d207580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h18 (q : Pattern) (ha : d205554 q = 1) (hb : d207581 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d205554, d207581, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d205554, d207581, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h19 (q : Pattern) (ha : d205555 q = 1) (hb : d207582 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d205555, d207582, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d205555, d207582, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro48658 (p : Pattern) (ha : d205561 p = 1) (hb : d207588 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d205556 q = 1) (hb : d207583 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d205556, d207583, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d205556, d207583, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48657 q ha hb
  have h2 (q : Pattern) (ha : d205557 q = 1) (hb : d207584 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d205557, d207584, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d205557, d207584, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d205558 q = 1) (hb : d207585 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d205558, d207585, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d205558, d207585, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d205559 q = 1) (hb : d207586 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d205559, d207586, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d205559, d207586, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d205560 q = 1) (hb : d207587 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d205560, d207587, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d205560, d207587, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d205561 q = 1) (hb : d207588 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d205561, d207588, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d205561, d207588, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro48659 (p : Pattern) (ha : d205697 p = 1) (hb : d207188 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d205658 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d205667 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d205686 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d205632 q = 1) (hb : d207183 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d205632, d207183, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48536 q ha hb
    | true =>
      simp only [d205632, d207183, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48537 q ha hb
  have h5 (q : Pattern) (ha : d205687 q = 1) (hb : d207184 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d205687, d207184, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d205687, d207184, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d205693 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d205694 q = 1) (hb : d207185 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d205694, d207185, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d205694, d207185, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d205695 q = 1) (hb : d207186 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d205695, d207186, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d205695, d207186, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d205696 q = 1) (hb : d207187 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d205696, d207187, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d205696, d207187, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d205697 q = 1) (hb : d207188 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d205697, d207188, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d205697, d207188, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro48660 (p : Pattern) (ha : d205718 p = 1) (hb : d207198 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d205658 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d205667 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d205686 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d205632 q = 1) (hb : d207183 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d205632, d207183, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48536 q ha hb
    | true =>
      simp only [d205632, d207183, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48537 q ha hb
  have h4 (q : Pattern) (ha : d205687 q = 1) (hb : d207184 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d205687, d207184, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d205687, d207184, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d205693 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d205694 q = 1) (hb : d207185 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d205694, d207185, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d205694, d207185, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d205695 q = 1) (hb : d207186 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d205695, d207186, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d205695, d207186, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d205696 q = 1) (hb : d207187 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d205696, d207187, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d205696, d207187, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d205703 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d205708 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d205710 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d205642 q = 1) (hb : d207193 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d205642, d207193, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48539 q ha hb
    | true =>
      simp only [d205642, d207193, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48540 q ha hb
  have h13 (q : Pattern) (ha : d205711 q = 1) (hb : d207194 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d205711, d207194, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
    | true =>
      simp only [d205711, d207194, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d205714 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d205715 q = 1) (hb : d207195 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d205715, d207195, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d205715, d207195, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d205716 q = 1) (hb : d207196 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d205716, d207196, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
    | true =>
      simp only [d205716, d207196, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d205717 q = 1) (hb : d207197 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d205717, d207197, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
    | true =>
      simp only [d205717, d207197, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d205718 q = 1) (hb : d207198 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d205718, d207198, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d205718, d207198, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro48661 (p : Pattern) (ha : d205738 p = 1) (hb : d207595 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d205710 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d205642 q = 1) (hb : d207193 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d205642, d207193, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48539 q ha hb
    | true =>
      simp only [d205642, d207193, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48540 q ha hb
  have h3 (q : Pattern) (ha : d205711 q = 1) (hb : d207194 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d205711, d207194, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d205711, d207194, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d205714 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d205715 q = 1) (hb : d207195 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d205715, d207195, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d205715, d207195, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d205736 q = 1) (hb : d207196 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d205736, d207196, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d205736, d207196, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d205737 q = 1) (hb : d207197 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d205737, d207197, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d205737, d207197, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d205738 q = 1) (hb : d207595 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d205738, d207595, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d205738, d207595, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro48662 (p : Pattern) (ha : d205807 p = 1) (hb : d207604 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d205794 q = 1) (hb : d207372 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d205794, d207372, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48573 q ha hb
    | true =>
      simp only [d205794, d207372, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d205795 q = 1) (hb : d207373 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d205795, d207373, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d205795, d207373, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d205802 q = 1) (hb : d207362 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d205802, d207362, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48571 q ha hb
    | true =>
      simp only [d205802, d207362, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d205803 q = 1) (hb : d207363 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d205803, d207363, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d205803, d207363, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d205804 q = 1) (hb : d207601 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d205804, d207601, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d205804, d207601, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d205805 q = 1) (hb : d207602 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d205805, d207602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d205805, d207602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d205806 q = 1) (hb : d207603 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d205806, d207603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d205806, d207603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d205807 q = 1) (hb : d207604 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d205807, d207604, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d205807, d207604, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro48663 (p : Pattern) (ha : d205824 p = 1) (hb : d207610 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d205808 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d205813 q = 1) (hb : d207605 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d205813, d207605, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48662 q ha hb
    | true =>
      simp only [d205813, d207605, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48576 q ha hb
  have h3 (q : Pattern) (ha : d205814 q = 1) (hb : d207606 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d205814, d207606, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d205814, d207606, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d205820 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d205821 q = 1) (hb : d207607 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d205821, d207607, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d205821, d207607, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d205822 q = 1) (hb : d207608 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d205822, d207608, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d205822, d207608, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d205823 q = 1) (hb : d207609 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d205823, d207609, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d205823, d207609, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d205824 q = 1) (hb : d207610 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d205824, d207610, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d205824, d207610, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro48664 (p : Pattern) (ha : d205837 p = 1) (hb : d207616 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d205650 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d205719 q = 1) (hb : d207199 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d205719, d207199, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48659 q ha hb
    | true =>
      simp only [d205719, d207199, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48660 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d205732 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d205733 q = 1) (hb : d207200 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d205733, d207200, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d205733, d207200, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d205734 q = 1) (hb : d207593 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d205734, d207593, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d205734, d207593, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d205735 q = 1) (hb : d207594 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d205735, d207594, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d205735, d207594, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d205739 q = 1) (hb : d207596 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d205739, d207596, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d205739, d207596, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48661 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d205741 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d205742 q = 1) (hb : d207597 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d205742, d207597, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d205742, d207597, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d205743 q = 1) (hb : d207598 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d205743, d207598, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d205743, d207598, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h11 (q : Pattern) (ha : d205744 q = 1) (hb : d207599 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d205744, d207599, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d205744, d207599, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h12 (q : Pattern) (ha : d205745 q = 1) (hb : d207600 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d205745, d207600, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d205745, d207600, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d205825 q = 1) (hb : d207611 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d205825, d207611, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d205825, d207611, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48663 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d205832 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d205833 q = 1) (hb : d207612 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d205833, d207612, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d205833, d207612, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d205834 q = 1) (hb : d207613 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d205834, d207613, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d205834, d207613, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h17 (q : Pattern) (ha : d205835 q = 1) (hb : d207614 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d205835, d207614, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d205835, d207614, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h18 (q : Pattern) (ha : d205836 q = 1) (hb : d207615 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d205836, d207615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d205836, d207615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h19 (q : Pattern) (ha : d205837 q = 1) (hb : d207616 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d205837, d207616, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d205837, d207616, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro48665 (p : Pattern) (ha : d205843 p = 1) (hb : d207622 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d205838 q = 1) (hb : d207617 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d205838, d207617, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d205838, d207617, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48664 q ha hb
  have h2 (q : Pattern) (ha : d205839 q = 1) (hb : d207618 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d205839, d207618, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d205839, d207618, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d205840 q = 1) (hb : d207619 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d205840, d207619, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d205840, d207619, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d205841 q = 1) (hb : d207620 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d205841, d207620, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d205841, d207620, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d205842 q = 1) (hb : d207621 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d205842, d207621, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d205842, d207621, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d205843 q = 1) (hb : d207622 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d205843, d207622, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d205843, d207622, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro48666 (p : Pattern) (ha : d205849 p = 1) (hb : d207628 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d204726 q = 1) (hb : d207497 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d204726, d207497, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48632 q ha hb
    | true =>
      simp only [d204726, d207497, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48638 q ha hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d204953 q = 1) (hb : d207524 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d204953, d207524, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d204953, d207524, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48644 q ha hb
  have h3 (q : Pattern) (ha : d204954 q = 1) (hb : d207525 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d204954, d207525, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d204954, d207525, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d205257 q = 1) (hb : d207556 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d205257, d207556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d205257, d207556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48651 q ha hb
  have h5 (q : Pattern) (ha : d205258 q = 1) (hb : d207557 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d205258, d207557, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d205258, d207557, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d205259 q = 1) (hb : d207558 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d205259, d207558, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d205259, d207558, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d205562 q = 1) (hb : d207589 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d205562, d207589, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d205562, d207589, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48658 q ha hb
  have h8 (q : Pattern) (ha : d205563 q = 1) (hb : d207590 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d205563, d207590, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d205563, d207590, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d205564 q = 1) (hb : d207591 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d205564, d207591, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d205564, d207591, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d205565 q = 1) (hb : d207592 q = 1) : d0 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d205565, d207592, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d205565, d207592, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d205844 q = 1) (hb : d207623 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d205844, d207623, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d205844, d207623, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48665 q ha hb
  have h12 (q : Pattern) (ha : d205845 q = 1) (hb : d207624 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d205845, d207624, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d205845, d207624, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d205846 q = 1) (hb : d207625 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d205846, d207625, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d205846, d207625, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d205847 q = 1) (hb : d207626 q = 1) : d0 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d205847, d207626, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d205847, d207626, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d205848 q = 1) (hb : d207627 q = 1) : d0 q = 1 := by
    cases bit : q 10250 with
    | false =>
      simp only [d205848, d207627, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d205848, d207627, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d205849 q = 1) (hb : d207628 q = 1) : d0 q = 1 := by
    cases bit : q 260 with
    | false =>
      simp only [d205849, d207628, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d205849, d207628, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  exact h16 p ha hb
theorem andIntro48667 (p : Pattern) (ha : d205855 p = 1) (hb : d207634 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d205850 q = 1) (hb : d207629 q = 1) : d0 q = 1 := by
    cases bit : q 259 with
    | false =>
      simp only [d205850, d207629, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48666 q ha hb
    | true =>
      simp only [d205850, d207629, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d205851 q = 1) (hb : d207630 q = 1) : d0 q = 1 := by
    cases bit : q 258 with
    | false =>
      simp only [d205851, d207630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d205851, d207630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d205852 q = 1) (hb : d207631 q = 1) : d0 q = 1 := by
    cases bit : q 257 with
    | false =>
      simp only [d205852, d207631, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d205852, d207631, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d205853 q = 1) (hb : d207632 q = 1) : d0 q = 1 := by
    cases bit : q 256 with
    | false =>
      simp only [d205853, d207632, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d205853, d207632, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d205854 q = 1) (hb : d207633 q = 1) : d0 q = 1 := by
    cases bit : q 255 with
    | false =>
      simp only [d205854, d207633, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d205854, d207633, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d205855 q = 1) (hb : d207634 q = 1) : d0 q = 1 := by
    cases bit : q 254 with
    | false =>
      simp only [d205855, d207634, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d205855, d207634, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro48668 (p : Pattern) (ha : d205861 p = 1) (hb : d207640 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d205856 q = 1) (hb : d207635 q = 1) : d0 q = 1 := by
    cases bit : q 253 with
    | false =>
      simp only [d205856, d207635, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48667 q ha hb
    | true =>
      simp only [d205856, d207635, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d205857 q = 1) (hb : d207636 q = 1) : d0 q = 1 := by
    cases bit : q 252 with
    | false =>
      simp only [d205857, d207636, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d205857, d207636, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d205858 q = 1) (hb : d207637 q = 1) : d0 q = 1 := by
    cases bit : q 251 with
    | false =>
      simp only [d205858, d207637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d205858, d207637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d205859 q = 1) (hb : d207638 q = 1) : d0 q = 1 := by
    cases bit : q 250 with
    | false =>
      simp only [d205859, d207638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d205859, d207638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d205860 q = 1) (hb : d207639 q = 1) : d0 q = 1 := by
    cases bit : q 249 with
    | false =>
      simp only [d205860, d207639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d205860, d207639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d205861 q = 1) (hb : d207640 q = 1) : d0 q = 1 := by
    cases bit : q 245 with
    | false =>
      simp only [d205861, d207640, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d205861, d207640, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro48669 (p : Pattern) (ha : d205867 p = 1) (hb : d207646 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d205862 q = 1) (hb : d207641 q = 1) : d0 q = 1 := by
    cases bit : q 200 with
    | false =>
      simp only [d205862, d207641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48668 q ha hb
    | true =>
      simp only [d205862, d207641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d205863 q = 1) (hb : d207642 q = 1) : d0 q = 1 := by
    cases bit : q 199 with
    | false =>
      simp only [d205863, d207642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d205863, d207642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d205864 q = 1) (hb : d207643 q = 1) : d0 q = 1 := by
    cases bit : q 186 with
    | false =>
      simp only [d205864, d207643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d205864, d207643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d205865 q = 1) (hb : d207644 q = 1) : d0 q = 1 := by
    cases bit : q 185 with
    | false =>
      simp only [d205865, d207644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d205865, d207644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d205866 q = 1) (hb : d207645 q = 1) : d0 q = 1 := by
    cases bit : q 184 with
    | false =>
      simp only [d205866, d207645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d205866, d207645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d205867 q = 1) (hb : d207646 q = 1) : d0 q = 1 := by
    cases bit : q 181 with
    | false =>
      simp only [d205867, d207646, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d205867, d207646, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro48670 (p : Pattern) (ha : d205873 p = 1) (hb : d207652 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d205868 q = 1) (hb : d207647 q = 1) : d0 q = 1 := by
    cases bit : q 177 with
    | false =>
      simp only [d205868, d207647, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48669 q ha hb
    | true =>
      simp only [d205868, d207647, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d205869 q = 1) (hb : d207648 q = 1) : d0 q = 1 := by
    cases bit : q 164 with
    | false =>
      simp only [d205869, d207648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d205869, d207648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d205870 q = 1) (hb : d207649 q = 1) : d0 q = 1 := by
    cases bit : q 156 with
    | false =>
      simp only [d205870, d207649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d205870, d207649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d205871 q = 1) (hb : d207650 q = 1) : d0 q = 1 := by
    cases bit : q 155 with
    | false =>
      simp only [d205871, d207650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d205871, d207650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d205872 q = 1) (hb : d207651 q = 1) : d0 q = 1 := by
    cases bit : q 134 with
    | false =>
      simp only [d205872, d207651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d205872, d207651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d205873 q = 1) (hb : d207652 q = 1) : d0 q = 1 := by
    cases bit : q 133 with
    | false =>
      simp only [d205873, d207652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d205873, d207652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro48671 (p : Pattern) (ha : d205879 p = 1) (hb : d207658 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d205874 q = 1) (hb : d207653 q = 1) : d0 q = 1 := by
    cases bit : q 120 with
    | false =>
      simp only [d205874, d207653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48670 q ha hb
    | true =>
      simp only [d205874, d207653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d205875 q = 1) (hb : d207654 q = 1) : d0 q = 1 := by
    cases bit : q 118 with
    | false =>
      simp only [d205875, d207654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d205875, d207654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d205876 q = 1) (hb : d207655 q = 1) : d0 q = 1 := by
    cases bit : q 114 with
    | false =>
      simp only [d205876, d207655, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d205876, d207655, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d205877 q = 1) (hb : d207656 q = 1) : d0 q = 1 := by
    cases bit : q 111 with
    | false =>
      simp only [d205877, d207656, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d205877, d207656, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d205878 q = 1) (hb : d207657 q = 1) : d0 q = 1 := by
    cases bit : q 98 with
    | false =>
      simp only [d205878, d207657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d205878, d207657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d205879 q = 1) (hb : d207658 q = 1) : d0 q = 1 := by
    cases bit : q 97 with
    | false =>
      simp only [d205879, d207658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d205879, d207658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro48672 (p : Pattern) (ha : d205885 p = 1) (hb : d207664 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d205880 q = 1) (hb : d207659 q = 1) : d0 q = 1 := by
    cases bit : q 94 with
    | false =>
      simp only [d205880, d207659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48671 q ha hb
    | true =>
      simp only [d205880, d207659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d205881 q = 1) (hb : d207660 q = 1) : d0 q = 1 := by
    cases bit : q 76 with
    | false =>
      simp only [d205881, d207660, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d205881, d207660, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d205882 q = 1) (hb : d207661 q = 1) : d0 q = 1 := by
    cases bit : q 67 with
    | false =>
      simp only [d205882, d207661, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d205882, d207661, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d205883 q = 1) (hb : d207662 q = 1) : d0 q = 1 := by
    cases bit : q 52 with
    | false =>
      simp only [d205883, d207662, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d205883, d207662, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d205884 q = 1) (hb : d207663 q = 1) : d0 q = 1 := by
    cases bit : q 47 with
    | false =>
      simp only [d205884, d207663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d205884, d207663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d205885 q = 1) (hb : d207664 q = 1) : d0 q = 1 := by
    cases bit : q 46 with
    | false =>
      simp only [d205885, d207664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d205885, d207664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro48673 (p : Pattern) (ha : d205891 p = 1) (hb : d207670 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d205886 q = 1) (hb : d207665 q = 1) : d0 q = 1 := by
    cases bit : q 45 with
    | false =>
      simp only [d205886, d207665, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48672 q ha hb
    | true =>
      simp only [d205886, d207665, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d205887 q = 1) (hb : d207666 q = 1) : d0 q = 1 := by
    cases bit : q 30 with
    | false =>
      simp only [d205887, d207666, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d205887, d207666, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d205888 q = 1) (hb : d207667 q = 1) : d0 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d205888, d207667, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d205888, d207667, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d205889 q = 1) (hb : d207668 q = 1) : d0 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d205889, d207668, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d205889, d207668, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d205890 q = 1) (hb : d207669 q = 1) : d0 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d205890, d207669, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d205890, d207669, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d205891 q = 1) (hb : d207670 q = 1) : d0 q = 1 := by
    cases bit : q 25 with
    | false =>
      simp only [d205891, d207670, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d205891, d207670, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro48674 (p : Pattern) (ha : d205975 p = 1) (hb : d207675 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d202409 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d202415 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d202439 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d205913 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d205971 q = 1) (hb : d207671 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d205971, d207671, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d205971, d207671, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d202332 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d205972 q = 1) (hb : d207672 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d205972, d207672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d205972, d207672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d205973 q = 1) (hb : d207673 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d205973, d207673, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d205973, d207673, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d205974 q = 1) (hb : d207674 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d205974, d207674, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d205974, d207674, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d205975 q = 1) (hb : d207675 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d205975, d207675, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d205975, d207675, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro48675 (p : Pattern) (ha : d205982 p = 1) (hb : d207680 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d202409 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d202415 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d202439 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d205913 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d205971 q = 1) (hb : d207671 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d205971, d207671, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d205971, d207671, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d202332 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d205972 q = 1) (hb : d207672 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d205972, d207672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d205972, d207672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d205973 q = 1) (hb : d207673 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d205973, d207673, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d205973, d207673, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d205974 q = 1) (hb : d207674 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d205974, d207674, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d205974, d207674, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d202473 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d202477 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d202479 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d205920 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d205978 q = 1) (hb : d207676 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d205978, d207676, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d205978, d207676, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d202339 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d205979 q = 1) (hb : d207677 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d205979, d207677, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d205979, d207677, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d205980 q = 1) (hb : d207678 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d205980, d207678, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d205980, d207678, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d205981 q = 1) (hb : d207679 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d205981, d207679, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d205981, d207679, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d205982 q = 1) (hb : d207680 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d205982, d207680, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d205982, d207680, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro48676 (p : Pattern) (ha : d206194 p = 1) (hb : d207687 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d202479 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d205920 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d205978 q = 1) (hb : d207676 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d205978, d207676, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d205978, d207676, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d202339 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d205979 q = 1) (hb : d207677 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d205979, d207677, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d205979, d207677, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d205980 q = 1) (hb : d207685 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d205980, d207685, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d205980, d207685, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d205981 q = 1) (hb : d207686 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d205981, d207686, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d205981, d207686, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d206194 q = 1) (hb : d207687 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d206194, d207687, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d206194, d207687, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro48677 (p : Pattern) (ha : d206240 p = 1) (hb : d207697 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d202519 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d205954 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d206236 q = 1) (hb : d207693 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d206236, d207693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d206236, d207693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d202373 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d206237 q = 1) (hb : d207694 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d206237, d207694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d206237, d207694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d206238 q = 1) (hb : d207695 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d206238, d207695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d206238, d207695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d206239 q = 1) (hb : d207696 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d206239, d207696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d206239, d207696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d206240 q = 1) (hb : d207697 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d206240, d207697, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d206240, d207697, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro48678 (p : Pattern) (ha : d207465 p = 1) (hb : d207703 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d202403 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d205983 q = 1) (hb : d207681 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d205983, d207681, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48674 q ha hb
    | true =>
      simp only [d205983, d207681, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48675 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d202489 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d205984 q = 1) (hb : d207682 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d205984, d207682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d205984, d207682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d207455 q = 1) (hb : d207683 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d207455, d207683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d207455, d207683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d207456 q = 1) (hb : d207684 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d207456, d207684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d207456, d207684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d206195 q = 1) (hb : d207688 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d206195, d207688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d206195, d207688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48676 q ha hb
  have h8 (q : Pattern) (ha : d207457 q = 1) (hb : d207689 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d207457, d207689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d207457, d207689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h9 (q : Pattern) (ha : d207458 q = 1) (hb : d207690 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d207458, d207690, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d207458, d207690, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h10 (q : Pattern) (ha : d207459 q = 1) (hb : d207691 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d207459, d207691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d207459, d207691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h11 (q : Pattern) (ha : d207460 q = 1) (hb : d207692 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d207460, d207692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d207460, d207692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d206241 q = 1) (hb : d207698 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d206241, d207698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d206241, d207698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48677 q ha hb
  have h13 (q : Pattern) (ha : d207461 q = 1) (hb : d207699 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d207461, d207699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d207461, d207699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h14 (q : Pattern) (ha : d207462 q = 1) (hb : d207700 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d207462, d207700, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d207462, d207700, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h15 (q : Pattern) (ha : d207463 q = 1) (hb : d207701 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d207463, d207701, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d207463, d207701, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h16 (q : Pattern) (ha : d207464 q = 1) (hb : d207702 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d207464, d207702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d207464, d207702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h17 (q : Pattern) (ha : d207465 q = 1) (hb : d207703 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d207465, d207703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d207465, d207703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  exact h17 p ha hb
theorem andIntro48679 (p : Pattern) (ha : d207471 p = 1) (hb : d207709 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d202388 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d207466 q = 1) (hb : d207704 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d207466, d207704, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d207466, d207704, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48678 q ha hb
  have h3 (q : Pattern) (ha : d207467 q = 1) (hb : d207705 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d207467, d207705, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d207467, d207705, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d207468 q = 1) (hb : d207706 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d207468, d207706, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d207468, d207706, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d207469 q = 1) (hb : d207707 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d207469, d207707, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d207469, d207707, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d207470 q = 1) (hb : d207708 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d207470, d207708, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d207470, d207708, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d207471 q = 1) (hb : d207709 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d207471, d207709, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d207471, d207709, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro48680 (p : Pattern) (ha : d206096 p = 1) (hb : d207714 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d202576 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d202582 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d202614 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d206020 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d206092 q = 1) (hb : d207710 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d206092, d207710, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d206092, d207710, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d202645 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d206093 q = 1) (hb : d207711 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d206093, d207711, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d206093, d207711, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d206094 q = 1) (hb : d207712 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d206094, d207712, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d206094, d207712, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d206095 q = 1) (hb : d207713 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d206095, d207713, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d206095, d207713, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d206096 q = 1) (hb : d207714 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d206096, d207714, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d206096, d207714, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro48681 (p : Pattern) (ha : d206103 p = 1) (hb : d207719 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d202576 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d202582 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d202614 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d206020 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d206092 q = 1) (hb : d207710 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d206092, d207710, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d206092, d207710, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d202645 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d206093 q = 1) (hb : d207711 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d206093, d207711, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d206093, d207711, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d206094 q = 1) (hb : d207712 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d206094, d207712, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d206094, d207712, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d206095 q = 1) (hb : d207713 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d206095, d207713, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d206095, d207713, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d202654 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d202658 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d202660 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d206036 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d206099 q = 1) (hb : d207715 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d206099, d207715, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d206099, d207715, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d202666 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d206100 q = 1) (hb : d207716 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d206100, d207716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d206100, d207716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d206101 q = 1) (hb : d207717 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d206101, d207717, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d206101, d207717, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d206102 q = 1) (hb : d207718 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d206102, d207718, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d206102, d207718, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d206103 q = 1) (hb : d207719 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d206103, d207719, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d206103, d207719, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro48682 (p : Pattern) (ha : d207474 p = 1) (hb : d207726 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d202660 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d206036 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d206099 q = 1) (hb : d207715 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d206099, d207715, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d206099, d207715, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d202666 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d206100 q = 1) (hb : d207716 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d206100, d207716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d206100, d207716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d206101 q = 1) (hb : d207724 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d206101, d207724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d206101, d207724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d206102 q = 1) (hb : d207725 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d206102, d207725, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d206102, d207725, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d207474 q = 1) (hb : d207726 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d207474, d207726, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d207474, d207726, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro48683 (p : Pattern) (ha : d207484 p = 1) (hb : d207736 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d202710 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d206074 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d207480 q = 1) (hb : d207732 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d207480, d207732, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d207480, d207732, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d202736 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d207481 q = 1) (hb : d207733 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d207481, d207733, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d207481, d207733, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d207482 q = 1) (hb : d207734 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d207482, d207734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d207482, d207734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d207483 q = 1) (hb : d207735 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d207483, d207735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d207483, d207735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d207484 q = 1) (hb : d207736 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d207484, d207736, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d207484, d207736, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro48684 (p : Pattern) (ha : d207490 p = 1) (hb : d207742 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d202570 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d206104 q = 1) (hb : d207720 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d206104, d207720, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48680 q ha hb
    | true =>
      simp only [d206104, d207720, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48681 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d202673 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d206105 q = 1) (hb : d207721 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d206105, d207721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d206105, d207721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d207472 q = 1) (hb : d207722 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d207472, d207722, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d207472, d207722, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d207473 q = 1) (hb : d207723 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d207473, d207723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d207473, d207723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d207475 q = 1) (hb : d207727 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d207475, d207727, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d207475, d207727, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48682 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d202682 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d207476 q = 1) (hb : d207728 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d207476, d207728, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d207476, d207728, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d207477 q = 1) (hb : d207729 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d207477, d207729, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d207477, d207729, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h11 (q : Pattern) (ha : d207478 q = 1) (hb : d207730 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d207478, d207730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d207478, d207730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h12 (q : Pattern) (ha : d207479 q = 1) (hb : d207731 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d207479, d207731, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d207479, d207731, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d207485 q = 1) (hb : d207737 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d207485, d207737, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d207485, d207737, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48683 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d202747 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d207486 q = 1) (hb : d207738 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d207486, d207738, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d207486, d207738, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d207487 q = 1) (hb : d207739 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d207487, d207739, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d207487, d207739, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h17 (q : Pattern) (ha : d207488 q = 1) (hb : d207740 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d207488, d207740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d207488, d207740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h18 (q : Pattern) (ha : d207489 q = 1) (hb : d207741 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d207489, d207741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d207489, d207741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h19 (q : Pattern) (ha : d207490 q = 1) (hb : d207742 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d207490, d207742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d207490, d207742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro48685 (p : Pattern) (ha : d207496 p = 1) (hb : d207748 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d207491 q = 1) (hb : d207743 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d207491, d207743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d207491, d207743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48684 q ha hb
  have h2 (q : Pattern) (ha : d207492 q = 1) (hb : d207744 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d207492, d207744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d207492, d207744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d207493 q = 1) (hb : d207745 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d207493, d207745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d207493, d207745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d207494 q = 1) (hb : d207746 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d207494, d207746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d207494, d207746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d207495 q = 1) (hb : d207747 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d207495, d207747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d207495, d207747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d207496 q = 1) (hb : d207748 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d207496, d207748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d207496, d207748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro48686 (p : Pattern) (ha : d206276 p = 1) (hb : d207754 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d202803 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d202812 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d202850 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d206271 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d206272 q = 1) (hb : d207750 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d206272, d207750, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d206272, d207750, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d202898 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d206273 q = 1) (hb : d207751 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d206273, d207751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d206273, d207751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d206274 q = 1) (hb : d207752 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d206274, d207752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d206274, d207752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d206275 q = 1) (hb : d207753 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d206275, d207753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d206275, d207753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d206276 q = 1) (hb : d207754 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d206276, d207754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d206276, d207754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro48687 (p : Pattern) (ha : d206286 p = 1) (hb : d207759 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d202803 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d202812 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d202850 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d206271 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d206272 q = 1) (hb : d207750 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d206272, d207750, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d206272, d207750, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d202898 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d206273 q = 1) (hb : d207751 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d206273, d207751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d206273, d207751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d206274 q = 1) (hb : d207752 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d206274, d207752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d206274, d207752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d206275 q = 1) (hb : d207753 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d206275, d207753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d206275, d207753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d202908 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d202913 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d202915 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d206281 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d206282 q = 1) (hb : d207755 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d206282, d207755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d206282, d207755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d202922 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d206283 q = 1) (hb : d207756 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d206283, d207756, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d206283, d207756, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d206284 q = 1) (hb : d207757 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d206284, d207757, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d206284, d207757, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d206285 q = 1) (hb : d207758 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d206285, d207758, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d206285, d207758, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d206286 q = 1) (hb : d207759 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d206286, d207759, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d206286, d207759, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro48688 (p : Pattern) (ha : d207500 p = 1) (hb : d207766 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d202915 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d206281 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d206282 q = 1) (hb : d207755 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d206282, d207755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d206282, d207755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d202922 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d206283 q = 1) (hb : d207756 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d206283, d207756, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d206283, d207756, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d206284 q = 1) (hb : d207764 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d206284, d207764, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d206284, d207764, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d206285 q = 1) (hb : d207765 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d206285, d207765, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d206285, d207765, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d207500 q = 1) (hb : d207766 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d207500, d207766, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d207500, d207766, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro48689 (p : Pattern) (ha : d207511 p = 1) (hb : d207776 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d202994 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d207506 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d207507 q = 1) (hb : d207772 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d207507, d207772, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d207507, d207772, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d203034 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d207508 q = 1) (hb : d207773 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d207508, d207773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d207508, d207773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d207509 q = 1) (hb : d207774 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d207509, d207774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d207509, d207774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d207510 q = 1) (hb : d207775 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d207510, d207775, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d207510, d207775, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d207511 q = 1) (hb : d207776 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d207511, d207776, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d207511, d207776, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro48690 (p : Pattern) (ha : d207517 p = 1) (hb : d207782 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d202795 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d206287 q = 1) (hb : d207760 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d206287, d207760, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48686 q ha hb
    | true =>
      simp only [d206287, d207760, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48687 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d202940 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d206288 q = 1) (hb : d207761 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d206288, d207761, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d206288, d207761, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d207498 q = 1) (hb : d207762 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d207498, d207762, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d207498, d207762, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d207499 q = 1) (hb : d207763 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d207499, d207763, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d207499, d207763, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d207501 q = 1) (hb : d207767 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d207501, d207767, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d207501, d207767, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48688 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d202949 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d207502 q = 1) (hb : d207768 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d207502, d207768, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d207502, d207768, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d207503 q = 1) (hb : d207769 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d207503, d207769, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d207503, d207769, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h11 (q : Pattern) (ha : d207504 q = 1) (hb : d207770 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d207504, d207770, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d207504, d207770, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h12 (q : Pattern) (ha : d207505 q = 1) (hb : d207771 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d207505, d207771, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d207505, d207771, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d207512 q = 1) (hb : d207777 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d207512, d207777, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d207512, d207777, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48689 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d203050 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d207513 q = 1) (hb : d207778 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d207513, d207778, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d207513, d207778, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d207514 q = 1) (hb : d207779 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d207514, d207779, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d207514, d207779, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h17 (q : Pattern) (ha : d207515 q = 1) (hb : d207780 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d207515, d207780, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d207515, d207780, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h18 (q : Pattern) (ha : d207516 q = 1) (hb : d207781 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d207516, d207781, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d207516, d207781, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h19 (q : Pattern) (ha : d207517 q = 1) (hb : d207782 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d207517, d207782, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d207517, d207782, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro48691 (p : Pattern) (ha : d207523 p = 1) (hb : d207788 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d207518 q = 1) (hb : d207783 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d207518, d207783, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d207518, d207783, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48690 q ha hb
  have h2 (q : Pattern) (ha : d207519 q = 1) (hb : d207784 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d207519, d207784, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d207519, d207784, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d207520 q = 1) (hb : d207785 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d207520, d207785, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d207520, d207785, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d207521 q = 1) (hb : d207786 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d207521, d207786, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d207521, d207786, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d207522 q = 1) (hb : d207787 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d207522, d207787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d207522, d207787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d207523 q = 1) (hb : d207788 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d207523, d207788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d207523, d207788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro48692 (p : Pattern) (ha : d206550 p = 1) (hb : d207795 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d203153 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d203162 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d203200 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d206545 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d206546 q = 1) (hb : d207791 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d206546, d207791, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d206546, d207791, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d203277 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d206547 q = 1) (hb : d207792 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d206547, d207792, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d206547, d207792, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d206548 q = 1) (hb : d207793 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d206548, d207793, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d206548, d207793, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d206549 q = 1) (hb : d207794 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d206549, d207794, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d206549, d207794, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d206550 q = 1) (hb : d207795 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d206550, d207795, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d206550, d207795, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro48693 (p : Pattern) (ha : d206560 p = 1) (hb : d207800 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d203153 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d203162 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d203200 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d206545 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d206546 q = 1) (hb : d207791 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d206546, d207791, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d206546, d207791, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d203277 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d206547 q = 1) (hb : d207792 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d206547, d207792, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d206547, d207792, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d206548 q = 1) (hb : d207793 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d206548, d207793, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d206548, d207793, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d206549 q = 1) (hb : d207794 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d206549, d207794, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d206549, d207794, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d203287 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d203292 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d203294 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d206555 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d206556 q = 1) (hb : d207796 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d206556, d207796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d206556, d207796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d203301 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d206557 q = 1) (hb : d207797 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d206557, d207797, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d206557, d207797, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d206558 q = 1) (hb : d207798 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d206558, d207798, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d206558, d207798, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d206559 q = 1) (hb : d207799 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d206559, d207799, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d206559, d207799, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d206560 q = 1) (hb : d207800 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d206560, d207800, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d206560, d207800, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro48694 (p : Pattern) (ha : d207528 p = 1) (hb : d207807 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d203294 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d206555 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d206556 q = 1) (hb : d207796 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d206556, d207796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d206556, d207796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d203301 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d206557 q = 1) (hb : d207797 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d206557, d207797, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d206557, d207797, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d206558 q = 1) (hb : d207805 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d206558, d207805, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d206558, d207805, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d206559 q = 1) (hb : d207806 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d206559, d207806, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d206559, d207806, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d207528 q = 1) (hb : d207807 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d207528, d207807, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d207528, d207807, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro48695 (p : Pattern) (ha : d207543 p = 1) (hb : d207817 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d203403 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d207538 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d207539 q = 1) (hb : d207813 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d207539, d207813, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d207539, d207813, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d203458 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d207540 q = 1) (hb : d207814 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d207540, d207814, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d207540, d207814, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d207541 q = 1) (hb : d207815 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d207541, d207815, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d207541, d207815, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d207542 q = 1) (hb : d207816 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d207542, d207816, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d207542, d207816, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d207543 q = 1) (hb : d207817 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d207543, d207817, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d207543, d207817, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro48696 (p : Pattern) (ha : d207549 p = 1) (hb : d207823 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d203145 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d206561 q = 1) (hb : d207801 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d206561, d207801, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48692 q ha hb
    | true =>
      simp only [d206561, d207801, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48693 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d203319 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d206562 q = 1) (hb : d207802 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d206562, d207802, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d206562, d207802, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d207526 q = 1) (hb : d207803 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d207526, d207803, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d207526, d207803, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d207527 q = 1) (hb : d207804 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d207527, d207804, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d207527, d207804, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d207529 q = 1) (hb : d207808 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d207529, d207808, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d207529, d207808, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48694 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d203328 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d207530 q = 1) (hb : d207809 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d207530, d207809, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d207530, d207809, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d207531 q = 1) (hb : d207810 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d207531, d207810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d207531, d207810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h11 (q : Pattern) (ha : d207532 q = 1) (hb : d207811 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d207532, d207811, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d207532, d207811, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h12 (q : Pattern) (ha : d207533 q = 1) (hb : d207812 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d207533, d207812, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d207533, d207812, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d207544 q = 1) (hb : d207818 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d207544, d207818, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d207544, d207818, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48695 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d203474 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d207545 q = 1) (hb : d207819 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d207545, d207819, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d207545, d207819, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d207546 q = 1) (hb : d207820 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d207546, d207820, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d207546, d207820, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h17 (q : Pattern) (ha : d207547 q = 1) (hb : d207821 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d207547, d207821, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d207547, d207821, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h18 (q : Pattern) (ha : d207548 q = 1) (hb : d207822 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d207548, d207822, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d207548, d207822, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h19 (q : Pattern) (ha : d207549 q = 1) (hb : d207823 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d207549, d207823, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d207549, d207823, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro48697 (p : Pattern) (ha : d207555 p = 1) (hb : d207829 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d207550 q = 1) (hb : d207824 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d207550, d207824, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d207550, d207824, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48696 q ha hb
  have h2 (q : Pattern) (ha : d207551 q = 1) (hb : d207825 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d207551, d207825, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d207551, d207825, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d207552 q = 1) (hb : d207826 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d207552, d207826, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d207552, d207826, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d207553 q = 1) (hb : d207827 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d207553, d207827, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d207553, d207827, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d207554 q = 1) (hb : d207828 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d207554, d207828, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d207554, d207828, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d207555 q = 1) (hb : d207829 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d207555, d207829, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d207555, d207829, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro48698 (p : Pattern) (ha : d206878 p = 1) (hb : d207837 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d203584 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d203593 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d203625 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d206873 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d206874 q = 1) (hb : d207833 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d206874, d207833, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d206874, d207833, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d203708 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d206875 q = 1) (hb : d207834 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d206875, d207834, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d206875, d207834, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d206876 q = 1) (hb : d207835 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d206876, d207835, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d206876, d207835, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d206877 q = 1) (hb : d207836 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d206877, d207836, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d206877, d207836, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d206878 q = 1) (hb : d207837 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d206878, d207837, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d206878, d207837, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro48699 (p : Pattern) (ha : d206888 p = 1) (hb : d207842 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d203584 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d203593 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d203625 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d206873 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d206874 q = 1) (hb : d207833 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d206874, d207833, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d206874, d207833, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d203708 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d206875 q = 1) (hb : d207834 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d206875, d207834, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d206875, d207834, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d206876 q = 1) (hb : d207835 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d206876, d207835, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d206876, d207835, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d206877 q = 1) (hb : d207836 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d206877, d207836, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d206877, d207836, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d203718 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d203723 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d203725 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d206883 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d206884 q = 1) (hb : d207838 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d206884, d207838, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d206884, d207838, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d203732 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d206885 q = 1) (hb : d207839 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d206885, d207839, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d206885, d207839, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d206886 q = 1) (hb : d207840 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d206886, d207840, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d206886, d207840, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d206887 q = 1) (hb : d207841 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d206887, d207841, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d206887, d207841, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d206888 q = 1) (hb : d207842 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d206888, d207842, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d206888, d207842, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro48700 (p : Pattern) (ha : d207561 p = 1) (hb : d207849 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d203725 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d206883 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d206884 q = 1) (hb : d207838 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d206884, d207838, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d206884, d207838, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d203732 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d206885 q = 1) (hb : d207839 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d206885, d207839, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d206885, d207839, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d206886 q = 1) (hb : d207847 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d206886, d207847, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d206886, d207847, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d206887 q = 1) (hb : d207848 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d206887, d207848, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d206887, d207848, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d207561 q = 1) (hb : d207849 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d207561, d207849, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d207561, d207849, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro48701 (p : Pattern) (ha : d207576 p = 1) (hb : d207859 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d203834 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d207571 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d207572 q = 1) (hb : d207855 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d207572, d207855, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d207572, d207855, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d203889 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d207573 q = 1) (hb : d207856 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d207573, d207856, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d207573, d207856, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d207574 q = 1) (hb : d207857 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d207574, d207857, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d207574, d207857, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d207575 q = 1) (hb : d207858 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d207575, d207858, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d207575, d207858, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d207576 q = 1) (hb : d207859 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d207576, d207859, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d207576, d207859, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro48702 (p : Pattern) (ha : d207582 p = 1) (hb : d207865 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d203576 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d206889 q = 1) (hb : d207843 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d206889, d207843, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48698 q ha hb
    | true =>
      simp only [d206889, d207843, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48699 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d203750 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d206890 q = 1) (hb : d207844 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d206890, d207844, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d206890, d207844, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d207559 q = 1) (hb : d207845 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d207559, d207845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d207559, d207845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d207560 q = 1) (hb : d207846 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d207560, d207846, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d207560, d207846, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d207562 q = 1) (hb : d207850 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d207562, d207850, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d207562, d207850, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48700 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d203759 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d207563 q = 1) (hb : d207851 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d207563, d207851, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d207563, d207851, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d207564 q = 1) (hb : d207852 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d207564, d207852, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d207564, d207852, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h11 (q : Pattern) (ha : d207565 q = 1) (hb : d207853 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d207565, d207853, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d207565, d207853, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h12 (q : Pattern) (ha : d207566 q = 1) (hb : d207854 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d207566, d207854, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d207566, d207854, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d207577 q = 1) (hb : d207860 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d207577, d207860, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d207577, d207860, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48701 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d203905 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d207578 q = 1) (hb : d207861 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d207578, d207861, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d207578, d207861, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d207579 q = 1) (hb : d207862 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d207579, d207862, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d207579, d207862, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h17 (q : Pattern) (ha : d207580 q = 1) (hb : d207863 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d207580, d207863, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d207580, d207863, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h18 (q : Pattern) (ha : d207581 q = 1) (hb : d207864 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d207581, d207864, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d207581, d207864, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h19 (q : Pattern) (ha : d207582 q = 1) (hb : d207865 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d207582, d207865, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d207582, d207865, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro48703 (p : Pattern) (ha : d207588 p = 1) (hb : d207871 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d207583 q = 1) (hb : d207866 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d207583, d207866, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d207583, d207866, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48702 q ha hb
  have h2 (q : Pattern) (ha : d207584 q = 1) (hb : d207867 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d207584, d207867, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d207584, d207867, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d207585 q = 1) (hb : d207868 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d207585, d207868, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d207585, d207868, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d207586 q = 1) (hb : d207869 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d207586, d207869, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d207586, d207869, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d207587 q = 1) (hb : d207870 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d207587, d207870, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d207587, d207870, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d207588 q = 1) (hb : d207871 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d207588, d207871, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d207588, d207871, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro48704 (p : Pattern) (ha : d207188 p = 1) (hb : d207880 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d204013 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d204022 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d204041 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d207183 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d207184 q = 1) (hb : d207876 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d207184, d207876, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d207184, d207876, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d204115 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d207185 q = 1) (hb : d207877 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d207185, d207877, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d207185, d207877, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d207186 q = 1) (hb : d207878 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d207186, d207878, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d207186, d207878, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d207187 q = 1) (hb : d207879 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d207187, d207879, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d207187, d207879, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d207188 q = 1) (hb : d207880 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d207188, d207880, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d207188, d207880, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro48705 (p : Pattern) (ha : d207198 p = 1) (hb : d207885 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d204013 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d204022 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d204041 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d207183 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d207184 q = 1) (hb : d207876 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d207184, d207876, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d207184, d207876, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d204115 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d207185 q = 1) (hb : d207877 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d207185, d207877, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d207185, d207877, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d207186 q = 1) (hb : d207878 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d207186, d207878, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d207186, d207878, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d207187 q = 1) (hb : d207879 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d207187, d207879, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d207187, d207879, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d204125 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d204130 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d204132 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d207193 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d207194 q = 1) (hb : d207881 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d207194, d207881, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d207194, d207881, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d204139 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d207195 q = 1) (hb : d207882 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d207195, d207882, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d207195, d207882, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d207196 q = 1) (hb : d207883 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d207196, d207883, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d207196, d207883, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d207197 q = 1) (hb : d207884 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d207197, d207884, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d207197, d207884, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d207198 q = 1) (hb : d207885 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d207198, d207885, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d207198, d207885, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro48706 (p : Pattern) (ha : d207595 p = 1) (hb : d207892 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d204132 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d207193 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d207194 q = 1) (hb : d207881 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d207194, d207881, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d207194, d207881, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d204139 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d207195 q = 1) (hb : d207882 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d207195, d207882, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d207195, d207882, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d207196 q = 1) (hb : d207890 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d207196, d207890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d207196, d207890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d207197 q = 1) (hb : d207891 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d207197, d207891, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d207197, d207891, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d207595 q = 1) (hb : d207892 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d207595, d207892, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d207595, d207892, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro48707 (p : Pattern) (ha : d207610 p = 1) (hb : d207902 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d204233 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d207605 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d207606 q = 1) (hb : d207898 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d207606, d207898, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d207606, d207898, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d204289 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d207607 q = 1) (hb : d207899 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d207607, d207899, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d207607, d207899, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d207608 q = 1) (hb : d207900 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d207608, d207900, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d207608, d207900, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d207609 q = 1) (hb : d207901 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d207609, d207901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d207609, d207901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d207610 q = 1) (hb : d207902 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d207610, d207902, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d207610, d207902, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro48708 (p : Pattern) (ha : d207616 p = 1) (hb : d207908 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d204005 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d207199 q = 1) (hb : d207886 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d207199, d207886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48704 q ha hb
    | true =>
      simp only [d207199, d207886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48705 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d204157 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d207200 q = 1) (hb : d207887 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d207200, d207887, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d207200, d207887, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d207593 q = 1) (hb : d207888 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d207593, d207888, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d207593, d207888, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d207594 q = 1) (hb : d207889 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d207594, d207889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d207594, d207889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d207596 q = 1) (hb : d207893 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d207596, d207893, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d207596, d207893, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48706 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d204166 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d207597 q = 1) (hb : d207894 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d207597, d207894, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d207597, d207894, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d207598 q = 1) (hb : d207895 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d207598, d207895, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d207598, d207895, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h11 (q : Pattern) (ha : d207599 q = 1) (hb : d207896 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d207599, d207896, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d207599, d207896, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h12 (q : Pattern) (ha : d207600 q = 1) (hb : d207897 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d207600, d207897, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d207600, d207897, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d207611 q = 1) (hb : d207903 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d207611, d207903, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d207611, d207903, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48707 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d204305 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d207612 q = 1) (hb : d207904 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d207612, d207904, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d207612, d207904, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d207613 q = 1) (hb : d207905 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d207613, d207905, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d207613, d207905, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h17 (q : Pattern) (ha : d207614 q = 1) (hb : d207906 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d207614, d207906, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d207614, d207906, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h18 (q : Pattern) (ha : d207615 q = 1) (hb : d207907 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d207615, d207907, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d207615, d207907, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h19 (q : Pattern) (ha : d207616 q = 1) (hb : d207908 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d207616, d207908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d207616, d207908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro48709 (p : Pattern) (ha : d207622 p = 1) (hb : d207914 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d207617 q = 1) (hb : d207909 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d207617, d207909, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d207617, d207909, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48708 q ha hb
  have h2 (q : Pattern) (ha : d207618 q = 1) (hb : d207910 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d207618, d207910, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d207618, d207910, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d207619 q = 1) (hb : d207911 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d207619, d207911, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d207619, d207911, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d207620 q = 1) (hb : d207912 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d207620, d207912, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d207620, d207912, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d207621 q = 1) (hb : d207913 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d207621, d207913, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d207621, d207913, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d207622 q = 1) (hb : d207914 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d207622, d207914, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d207622, d207914, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro48710 (p : Pattern) (ha : d207628 p = 1) (hb : d207920 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d207497 q = 1) (hb : d207749 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d207497, d207749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48679 q ha hb
    | true =>
      simp only [d207497, d207749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48685 q ha hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d207524 q = 1) (hb : d207789 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d207524, d207789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d207524, d207789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48691 q ha hb
  have h3 (q : Pattern) (ha : d207525 q = 1) (hb : d207790 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d207525, d207790, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d207525, d207790, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d207556 q = 1) (hb : d207830 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d207556, d207830, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d207556, d207830, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48697 q ha hb
  have h5 (q : Pattern) (ha : d207557 q = 1) (hb : d207831 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d207557, d207831, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d207557, d207831, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d207558 q = 1) (hb : d207832 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d207558, d207832, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d207558, d207832, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d207589 q = 1) (hb : d207872 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d207589, d207872, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d207589, d207872, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48703 q ha hb
  have h8 (q : Pattern) (ha : d207590 q = 1) (hb : d207873 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d207590, d207873, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d207590, d207873, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d207591 q = 1) (hb : d207874 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d207591, d207874, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d207591, d207874, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d207592 q = 1) (hb : d207875 q = 1) : d0 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d207592, d207875, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d207592, d207875, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d207623 q = 1) (hb : d207915 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d207623, d207915, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d207623, d207915, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48709 q ha hb
  have h12 (q : Pattern) (ha : d207624 q = 1) (hb : d207916 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d207624, d207916, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d207624, d207916, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d207625 q = 1) (hb : d207917 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d207625, d207917, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d207625, d207917, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d207626 q = 1) (hb : d207918 q = 1) : d0 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d207626, d207918, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d207626, d207918, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d207627 q = 1) (hb : d207919 q = 1) : d0 q = 1 := by
    cases bit : q 10250 with
    | false =>
      simp only [d207627, d207919, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d207627, d207919, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d207628 q = 1) (hb : d207920 q = 1) : d0 q = 1 := by
    cases bit : q 260 with
    | false =>
      simp only [d207628, d207920, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d207628, d207920, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  exact h16 p ha hb
theorem andIntro48711 (p : Pattern) (ha : d207634 p = 1) (hb : d207926 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d207629 q = 1) (hb : d207921 q = 1) : d0 q = 1 := by
    cases bit : q 259 with
    | false =>
      simp only [d207629, d207921, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48710 q ha hb
    | true =>
      simp only [d207629, d207921, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d207630 q = 1) (hb : d207922 q = 1) : d0 q = 1 := by
    cases bit : q 258 with
    | false =>
      simp only [d207630, d207922, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d207630, d207922, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d207631 q = 1) (hb : d207923 q = 1) : d0 q = 1 := by
    cases bit : q 257 with
    | false =>
      simp only [d207631, d207923, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d207631, d207923, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d207632 q = 1) (hb : d207924 q = 1) : d0 q = 1 := by
    cases bit : q 256 with
    | false =>
      simp only [d207632, d207924, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d207632, d207924, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d207633 q = 1) (hb : d207925 q = 1) : d0 q = 1 := by
    cases bit : q 255 with
    | false =>
      simp only [d207633, d207925, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d207633, d207925, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d207634 q = 1) (hb : d207926 q = 1) : d0 q = 1 := by
    cases bit : q 254 with
    | false =>
      simp only [d207634, d207926, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d207634, d207926, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro48712 (p : Pattern) (ha : d207640 p = 1) (hb : d207932 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d207635 q = 1) (hb : d207927 q = 1) : d0 q = 1 := by
    cases bit : q 253 with
    | false =>
      simp only [d207635, d207927, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48711 q ha hb
    | true =>
      simp only [d207635, d207927, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d207636 q = 1) (hb : d207928 q = 1) : d0 q = 1 := by
    cases bit : q 252 with
    | false =>
      simp only [d207636, d207928, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d207636, d207928, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d207637 q = 1) (hb : d207929 q = 1) : d0 q = 1 := by
    cases bit : q 251 with
    | false =>
      simp only [d207637, d207929, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d207637, d207929, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d207638 q = 1) (hb : d207930 q = 1) : d0 q = 1 := by
    cases bit : q 250 with
    | false =>
      simp only [d207638, d207930, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d207638, d207930, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d207639 q = 1) (hb : d207931 q = 1) : d0 q = 1 := by
    cases bit : q 249 with
    | false =>
      simp only [d207639, d207931, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d207639, d207931, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d207640 q = 1) (hb : d207932 q = 1) : d0 q = 1 := by
    cases bit : q 245 with
    | false =>
      simp only [d207640, d207932, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d207640, d207932, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro48713 (p : Pattern) (ha : d207646 p = 1) (hb : d207938 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d207641 q = 1) (hb : d207933 q = 1) : d0 q = 1 := by
    cases bit : q 200 with
    | false =>
      simp only [d207641, d207933, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48712 q ha hb
    | true =>
      simp only [d207641, d207933, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d207642 q = 1) (hb : d207934 q = 1) : d0 q = 1 := by
    cases bit : q 199 with
    | false =>
      simp only [d207642, d207934, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d207642, d207934, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d207643 q = 1) (hb : d207935 q = 1) : d0 q = 1 := by
    cases bit : q 186 with
    | false =>
      simp only [d207643, d207935, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d207643, d207935, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d207644 q = 1) (hb : d207936 q = 1) : d0 q = 1 := by
    cases bit : q 185 with
    | false =>
      simp only [d207644, d207936, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d207644, d207936, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d207645 q = 1) (hb : d207937 q = 1) : d0 q = 1 := by
    cases bit : q 184 with
    | false =>
      simp only [d207645, d207937, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d207645, d207937, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d207646 q = 1) (hb : d207938 q = 1) : d0 q = 1 := by
    cases bit : q 181 with
    | false =>
      simp only [d207646, d207938, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d207646, d207938, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro48714 (p : Pattern) (ha : d207652 p = 1) (hb : d207944 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d207647 q = 1) (hb : d207939 q = 1) : d0 q = 1 := by
    cases bit : q 177 with
    | false =>
      simp only [d207647, d207939, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48713 q ha hb
    | true =>
      simp only [d207647, d207939, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d207648 q = 1) (hb : d207940 q = 1) : d0 q = 1 := by
    cases bit : q 164 with
    | false =>
      simp only [d207648, d207940, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d207648, d207940, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d207649 q = 1) (hb : d207941 q = 1) : d0 q = 1 := by
    cases bit : q 156 with
    | false =>
      simp only [d207649, d207941, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d207649, d207941, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d207650 q = 1) (hb : d207942 q = 1) : d0 q = 1 := by
    cases bit : q 155 with
    | false =>
      simp only [d207650, d207942, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d207650, d207942, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d207651 q = 1) (hb : d207943 q = 1) : d0 q = 1 := by
    cases bit : q 134 with
    | false =>
      simp only [d207651, d207943, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d207651, d207943, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d207652 q = 1) (hb : d207944 q = 1) : d0 q = 1 := by
    cases bit : q 133 with
    | false =>
      simp only [d207652, d207944, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d207652, d207944, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro48715 (p : Pattern) (ha : d207658 p = 1) (hb : d207950 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d207653 q = 1) (hb : d207945 q = 1) : d0 q = 1 := by
    cases bit : q 120 with
    | false =>
      simp only [d207653, d207945, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48714 q ha hb
    | true =>
      simp only [d207653, d207945, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d207654 q = 1) (hb : d207946 q = 1) : d0 q = 1 := by
    cases bit : q 118 with
    | false =>
      simp only [d207654, d207946, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d207654, d207946, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d207655 q = 1) (hb : d207947 q = 1) : d0 q = 1 := by
    cases bit : q 114 with
    | false =>
      simp only [d207655, d207947, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d207655, d207947, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d207656 q = 1) (hb : d207948 q = 1) : d0 q = 1 := by
    cases bit : q 111 with
    | false =>
      simp only [d207656, d207948, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d207656, d207948, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d207657 q = 1) (hb : d207949 q = 1) : d0 q = 1 := by
    cases bit : q 98 with
    | false =>
      simp only [d207657, d207949, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d207657, d207949, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d207658 q = 1) (hb : d207950 q = 1) : d0 q = 1 := by
    cases bit : q 97 with
    | false =>
      simp only [d207658, d207950, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d207658, d207950, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro48716 (p : Pattern) (ha : d207664 p = 1) (hb : d207956 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d207659 q = 1) (hb : d207951 q = 1) : d0 q = 1 := by
    cases bit : q 94 with
    | false =>
      simp only [d207659, d207951, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48715 q ha hb
    | true =>
      simp only [d207659, d207951, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d207660 q = 1) (hb : d207952 q = 1) : d0 q = 1 := by
    cases bit : q 76 with
    | false =>
      simp only [d207660, d207952, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d207660, d207952, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d207661 q = 1) (hb : d207953 q = 1) : d0 q = 1 := by
    cases bit : q 67 with
    | false =>
      simp only [d207661, d207953, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d207661, d207953, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d207662 q = 1) (hb : d207954 q = 1) : d0 q = 1 := by
    cases bit : q 52 with
    | false =>
      simp only [d207662, d207954, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d207662, d207954, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d207663 q = 1) (hb : d207955 q = 1) : d0 q = 1 := by
    cases bit : q 47 with
    | false =>
      simp only [d207663, d207955, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d207663, d207955, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d207664 q = 1) (hb : d207956 q = 1) : d0 q = 1 := by
    cases bit : q 46 with
    | false =>
      simp only [d207664, d207956, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d207664, d207956, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro48717 (p : Pattern) (ha : d207670 p = 1) (hb : d207962 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d207665 q = 1) (hb : d207957 q = 1) : d0 q = 1 := by
    cases bit : q 45 with
    | false =>
      simp only [d207665, d207957, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48716 q ha hb
    | true =>
      simp only [d207665, d207957, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d207666 q = 1) (hb : d207958 q = 1) : d0 q = 1 := by
    cases bit : q 30 with
    | false =>
      simp only [d207666, d207958, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d207666, d207958, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d207667 q = 1) (hb : d207959 q = 1) : d0 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d207667, d207959, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d207667, d207959, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d207668 q = 1) (hb : d207960 q = 1) : d0 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d207668, d207960, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d207668, d207960, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d207669 q = 1) (hb : d207961 q = 1) : d0 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d207669, d207961, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d207669, d207961, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d207670 q = 1) (hb : d207962 q = 1) : d0 q = 1 := by
    cases bit : q 25 with
    | false =>
      simp only [d207670, d207962, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d207670, d207962, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro48718 (p : Pattern) (ha : d150326 p = 1) (hb : d207963 p = 1) : d150326 p = 1 := by
  have h0 (q : Pattern) (ha : d150326 q = 1) (hb : d207963 q = 1) : d150326 q = 1 := by
    exact ha
  exact h0 p ha hb
theorem andIntro48719 (p : Pattern) (ha : d20893 p = 1) (hb : d51995 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d751 q = 1) (hb : d51990 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d751, d51990, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33341 q ha hb
    | true =>
      simp only [d751, d51990, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d752 q = 1) (hb : d51991 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d752, d51991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d752, d51991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d753 q = 1) (hb : d51992 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d753, d51992, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d753, d51992, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d754 q = 1) (hb : d51993 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d754, d51993, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d754, d51993, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d25 q = 1) (hb : d51877 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d25, d51877, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro2 q ha hb
    | true =>
      simp only [d25, d51877, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d26 q = 1) (hb : d51878 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d26, d51878, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d26, d51878, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d27 q = 1) (hb : d51879 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d27, d51879, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d27, d51879, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d28 q = 1) (hb : d51880 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d28, d51880, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d28, d51880, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d20892 q = 1) (hb : d51994 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d20892, d51994, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d20892, d51994, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d29 q = 1) (hb : d51881 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d29, d51881, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d29, d51881, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d20893 q = 1) (hb : d51995 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d20893, d51995, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d20893, d51995, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro48720 (p : Pattern) (ha : d20899 p = 1) (hb : d52001 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d20894 q = 1) (hb : d51996 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d20894, d51996, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48719 q ha hb
    | true =>
      simp only [d20894, d51996, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro3 q ha hb
  have h2 (q : Pattern) (ha : d20895 q = 1) (hb : d51997 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d20895, d51997, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20895, d51997, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d20896 q = 1) (hb : d51998 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d20896, d51998, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20896, d51998, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d31 q = 1) (hb : d51883 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d31, d51883, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro3 q ha hb
    | true =>
      simp only [d31, d51883, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d32 q = 1) (hb : d51884 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d32, d51884, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d32, d51884, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d33 q = 1) (hb : d51885 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d33, d51885, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d33, d51885, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d20897 q = 1) (hb : d51999 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d20897, d51999, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d20897, d51999, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d34 q = 1) (hb : d51886 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d34, d51886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d34, d51886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d20898 q = 1) (hb : d52000 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d20898, d52000, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d20898, d52000, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d20899 q = 1) (hb : d52001 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d20899, d52001, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d20899, d52001, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h10 p ha hb
theorem andIntro48721 (p : Pattern) (ha : d20905 p = 1) (hb : d52007 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d20900 q = 1) (hb : d52002 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d20900, d52002, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48720 q ha hb
    | true =>
      simp only [d20900, d52002, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d20901 q = 1) (hb : d52003 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d20901, d52003, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20901, d52003, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d37 q = 1) (hb : d51889 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d37, d51889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4 q ha hb
    | true =>
      simp only [d37, d51889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d38 q = 1) (hb : d51890 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d38, d51890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d38, d51890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d20902 q = 1) (hb : d52004 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d20902, d52004, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d20902, d52004, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d20903 q = 1) (hb : d52005 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d20903, d52005, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d20903, d52005, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d20904 q = 1) (hb : d52006 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d20904, d52006, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d20904, d52006, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d20905 q = 1) (hb : d52007 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d20905, d52007, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20905, d52007, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro48722 (p : Pattern) (ha : d52013 p = 1) (hb : d150001 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d117 q = 1) (hb : d51969 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d117, d51969, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28 q ha hb
    | true =>
      simp only [d117, d51969, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d118 q = 1) (hb : d51970 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d118, d51970, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d118, d51970, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d119 q = 1) (hb : d51971 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d119, d51971, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d119, d51971, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d120 q = 1) (hb : d51972 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d120, d51972, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d120, d51972, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d124 q = 1) (hb : d51976 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d124, d51976, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29 q ha hb
    | true =>
      simp only [d124, d51976, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d125 q = 1) (hb : d51977 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d125, d51977, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d125, d51977, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d126 q = 1) (hb : d51978 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d126, d51978, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d126, d51978, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d20906 q = 1) (hb : d52008 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d20906, d52008, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48721 q ha hb
    | true =>
      simp only [d20906, d52008, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d51895 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d52009 q = 1) (hb : d149997 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d52009, d149997, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
    | true =>
      simp only [d52009, d149997, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
  have h11 (q : Pattern) (ha : d43 q = 1) (hb : d51895 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d43, d51895, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5 q ha hb
    | true =>
      simp only [d43, d51895, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d44 q = 1) (hb : d51896 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d44, d51896, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d44, d51896, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d52010 q = 1) (hb : d149998 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d52010, d149998, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d52010, d149998, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
  have h14 (q : Pattern) (ha : d52011 q = 1) (hb : d149999 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d52011, d149999, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
    | true =>
      simp only [d52011, d149999, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d52012 q = 1) (hb : d150000 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d52012, d150000, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d52012, d150000, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d52013 q = 1) (hb : d150001 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d52013, d150001, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d52013, d150001, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  exact h16 p ha hb
theorem andIntro48723 (p : Pattern) (ha : d20912 p = 1) (hb : d52023 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d20900 q = 1) (hb : d52002 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d20900, d52002, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48720 q ha hb
    | true =>
      simp only [d20900, d52002, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d20901 q = 1) (hb : d52003 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d20901, d52003, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20901, d52003, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d37 q = 1) (hb : d51889 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d37, d51889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4 q ha hb
    | true =>
      simp only [d37, d51889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d38 q = 1) (hb : d51890 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d38, d51890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d38, d51890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d20902 q = 1) (hb : d52004 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d20902, d52004, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d20902, d52004, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d20903 q = 1) (hb : d52005 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d20903, d52005, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d20903, d52005, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d20904 q = 1) (hb : d52006 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d20904, d52006, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d20904, d52006, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d20912 q = 1) (hb : d52023 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d20912, d52023, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d20912, d52023, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro48724 (p : Pattern) (ha : d52029 p = 1) (hb : d150006 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d117 q = 1) (hb : d51969 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d117, d51969, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28 q ha hb
    | true =>
      simp only [d117, d51969, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d118 q = 1) (hb : d51970 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d118, d51970, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d118, d51970, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d119 q = 1) (hb : d51971 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d119, d51971, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d119, d51971, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d120 q = 1) (hb : d51972 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d120, d51972, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d120, d51972, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d124 q = 1) (hb : d51976 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d124, d51976, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29 q ha hb
    | true =>
      simp only [d124, d51976, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d125 q = 1) (hb : d51977 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d125, d51977, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d125, d51977, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d126 q = 1) (hb : d51978 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d126, d51978, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d126, d51978, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d20906 q = 1) (hb : d52008 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d20906, d52008, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48721 q ha hb
    | true =>
      simp only [d20906, d52008, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d51895 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d52009 q = 1) (hb : d149997 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d52009, d149997, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
    | true =>
      simp only [d52009, d149997, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
  have h11 (q : Pattern) (ha : d43 q = 1) (hb : d51895 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d43, d51895, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5 q ha hb
    | true =>
      simp only [d43, d51895, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d44 q = 1) (hb : d51896 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d44, d51896, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d44, d51896, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d52010 q = 1) (hb : d149998 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d52010, d149998, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d52010, d149998, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
  have h14 (q : Pattern) (ha : d52011 q = 1) (hb : d149999 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d52011, d149999, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
    | true =>
      simp only [d52011, d149999, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d52012 q = 1) (hb : d150000 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d52012, d150000, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d52012, d150000, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d195 q = 1) (hb : d52015 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d195, d52015, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32 q ha hb
    | true =>
      simp only [d195, d52015, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h17 (q : Pattern) (ha : d196 q = 1) (hb : d52016 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d196, d52016, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d196, d52016, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d197 q = 1) (hb : d52017 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d197, d52017, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d197, d52017, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h19 (q : Pattern) (ha : d198 q = 1) (hb : d52018 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d198, d52018, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d198, d52018, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d200 q = 1) (hb : d52020 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d200, d52020, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33 q ha hb
    | true =>
      simp only [d200, d52020, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h21 (q : Pattern) (ha : d201 q = 1) (hb : d52021 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d201, d52021, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d201, d52021, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
  have h22 (q : Pattern) (ha : d202 q = 1) (hb : d52022 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d202, d52022, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d202, d52022, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h23 (q : Pattern) (ha : d20913 q = 1) (hb : d52024 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d20913, d52024, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48723 q ha hb
    | true =>
      simp only [d20913, d52024, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7 q ha hb
  have h24 (q : Pattern) (ha : d0 q = 1) (hb : d51902 q = 1) : d0 q = 1 := by
    exact ha
  have h25 (q : Pattern) (ha : d52025 q = 1) (hb : d150002 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d52025, d150002, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q hb ha
    | true =>
      simp only [d52025, d150002, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q hb ha
  have h26 (q : Pattern) (ha : d50 q = 1) (hb : d51902 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d50, d51902, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7 q ha hb
    | true =>
      simp only [d50, d51902, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h27 (q : Pattern) (ha : d51 q = 1) (hb : d51903 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d51, d51903, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h26 q ha hb
    | true =>
      simp only [d51, d51903, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h28 (q : Pattern) (ha : d52026 q = 1) (hb : d150003 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d52026, d150003, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q ha hb
    | true =>
      simp only [d52026, d150003, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h27 q hb ha
  have h29 (q : Pattern) (ha : d52027 q = 1) (hb : d150004 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d52027, d150004, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q hb ha
    | true =>
      simp only [d52027, d150004, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h28 q ha hb
  have h30 (q : Pattern) (ha : d52028 q = 1) (hb : d150005 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d52028, d150005, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q hb ha
    | true =>
      simp only [d52028, d150005, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h29 q ha hb
  have h31 (q : Pattern) (ha : d52029 q = 1) (hb : d150006 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d52029, d150006, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d52029, d150006, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h30 q ha hb
  exact h31 p ha hb
theorem andIntro48725 (p : Pattern) (ha : d52038 p = 1) (hb : d150013 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d20913 q = 1) (hb : d52024 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d20913, d52024, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48723 q ha hb
    | true =>
      simp only [d20913, d52024, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d51902 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d52025 q = 1) (hb : d150002 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d52025, d150002, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d52025, d150002, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d50 q = 1) (hb : d51902 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d50, d51902, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7 q ha hb
    | true =>
      simp only [d50, d51902, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d51 q = 1) (hb : d51903 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d51, d51903, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d51, d51903, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d52026 q = 1) (hb : d150003 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d52026, d150003, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d52026, d150003, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d52036 q = 1) (hb : d150011 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d52036, d150011, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d52036, d150011, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d52037 q = 1) (hb : d150012 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d52037, d150012, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d52037, d150012, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d52038 q = 1) (hb : d150013 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d52038, d150013, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d52038, d150013, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro48726 (p : Pattern) (ha : d20932 p = 1) (hb : d52049 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d971 q = 1) (hb : d52044 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d971, d52044, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d971, d52044, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33341 q ha hb
  have h2 (q : Pattern) (ha : d751 q = 1) (hb : d51990 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d751, d51990, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33341 q ha hb
    | true =>
      simp only [d751, d51990, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d972 q = 1) (hb : d52045 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d972, d52045, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d972, d52045, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d752 q = 1) (hb : d51991 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d752, d51991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d752, d51991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d973 q = 1) (hb : d52046 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d973, d52046, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d973, d52046, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d974 q = 1) (hb : d52047 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d974, d52047, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d974, d52047, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d66 q = 1) (hb : d51918 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d66, d51918, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d66, d51918, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro2 q ha hb
  have h8 (q : Pattern) (ha : d25 q = 1) (hb : d51877 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d25, d51877, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro2 q ha hb
    | true =>
      simp only [d25, d51877, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d67 q = 1) (hb : d51919 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d67, d51919, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d67, d51919, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d26 q = 1) (hb : d51878 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d26, d51878, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d26, d51878, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d68 q = 1) (hb : d51920 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d68, d51920, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d68, d51920, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d69 q = 1) (hb : d51921 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d69, d51921, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d69, d51921, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d20931 q = 1) (hb : d52048 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d20931, d52048, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d20931, d52048, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d70 q = 1) (hb : d51922 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d70, d51922, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d70, d51922, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d20932 q = 1) (hb : d52049 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d20932, d52049, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d20932, d52049, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro48727 (p : Pattern) (ha : d20938 p = 1) (hb : d52055 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d20933 q = 1) (hb : d52050 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d20933, d52050, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48726 q ha hb
    | true =>
      simp only [d20933, d52050, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10 q ha hb
  have h2 (q : Pattern) (ha : d20934 q = 1) (hb : d52051 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d20934, d52051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20934, d52051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d20935 q = 1) (hb : d52052 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d20935, d52052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20935, d52052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d72 q = 1) (hb : d51924 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d72, d51924, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10 q ha hb
    | true =>
      simp only [d72, d51924, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d73 q = 1) (hb : d51925 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d73, d51925, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d73, d51925, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d74 q = 1) (hb : d51926 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d74, d51926, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d74, d51926, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d20936 q = 1) (hb : d52053 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d20936, d52053, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d20936, d52053, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d75 q = 1) (hb : d51927 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d75, d51927, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d75, d51927, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d20937 q = 1) (hb : d52054 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d20937, d52054, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d20937, d52054, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d20938 q = 1) (hb : d52055 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d20938, d52055, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d20938, d52055, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h10 p ha hb
theorem andIntro48728 (p : Pattern) (ha : d20944 p = 1) (hb : d52061 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d20939 q = 1) (hb : d52056 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d20939, d52056, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48727 q ha hb
    | true =>
      simp only [d20939, d52056, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d20940 q = 1) (hb : d52057 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d20940, d52057, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20940, d52057, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d78 q = 1) (hb : d51930 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d78, d51930, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11 q ha hb
    | true =>
      simp only [d78, d51930, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d79 q = 1) (hb : d51931 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d79, d51931, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d79, d51931, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d20941 q = 1) (hb : d52058 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d20941, d52058, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d20941, d52058, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d20942 q = 1) (hb : d52059 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d20942, d52059, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d20942, d52059, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d20943 q = 1) (hb : d52060 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d20943, d52060, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d20943, d52060, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d20944 q = 1) (hb : d52061 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d20944, d52061, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d20944, d52061, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro48729 (p : Pattern) (ha : d52067 p = 1) (hb : d150023 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d20945 q = 1) (hb : d52062 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d20945, d52062, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48728 q ha hb
    | true =>
      simp only [d20945, d52062, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d51936 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d52063 q = 1) (hb : d150019 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d52063, d150019, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d52063, d150019, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d84 q = 1) (hb : d51936 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d84, d51936, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12 q ha hb
    | true =>
      simp only [d84, d51936, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d85 q = 1) (hb : d51937 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d85, d51937, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d85, d51937, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d52064 q = 1) (hb : d150020 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d52064, d150020, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d52064, d150020, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d52065 q = 1) (hb : d150021 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d52065, d150021, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d52065, d150021, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d52066 q = 1) (hb : d150022 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d52066, d150022, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d52066, d150022, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d52067 q = 1) (hb : d150023 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d52067, d150023, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d52067, d150023, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro48730 (p : Pattern) (ha : d52073 p = 1) (hb : d150029 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d105 q = 1) (hb : d51957 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d105, d51957, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d105, d51957, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro15 q ha hb
  have h2 (q : Pattern) (ha : d106 q = 1) (hb : d51958 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d106, d51958, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d106, d51958, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d112 q = 1) (hb : d51964 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d112, d51964, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro15 q ha hb
    | true =>
      simp only [d112, d51964, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16 q ha hb
  have h4 (q : Pattern) (ha : d113 q = 1) (hb : d51965 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d113, d51965, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d113, d51965, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d114 q = 1) (hb : d51966 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d114, d51966, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d114, d51966, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d52030 q = 1) (hb : d150007 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d52030, d150007, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48722 q ha hb
    | true =>
      simp only [d52030, d150007, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48724 q ha hb
  have h7 (q : Pattern) (ha : d214 q = 1) (hb : d52032 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d214, d52032, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17 q ha hb
    | true =>
      simp only [d214, d52032, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d52033 q = 1) (hb : d150008 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d52033, d150008, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d52033, d150008, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
  have h9 (q : Pattern) (ha : d52034 q = 1) (hb : d150009 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d52034, d150009, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d52034, d150009, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h10 (q : Pattern) (ha : d52035 q = 1) (hb : d150010 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d52035, d150010, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
    | true =>
      simp only [d52035, d150010, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d52039 q = 1) (hb : d150014 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d52039, d150014, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d52039, d150014, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48725 q ha hb
  have h12 (q : Pattern) (ha : d52040 q = 1) (hb : d150015 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d52040, d150015, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d52040, d150015, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d52041 q = 1) (hb : d150016 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d52041, d150016, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d52041, d150016, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h14 (q : Pattern) (ha : d52042 q = 1) (hb : d150017 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d52042, d150017, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d52042, d150017, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h15 (q : Pattern) (ha : d52043 q = 1) (hb : d150018 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d52043, d150018, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d52043, d150018, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d52068 q = 1) (hb : d150024 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d52068, d150024, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d52068, d150024, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48729 q ha hb
  have h17 (q : Pattern) (ha : d52069 q = 1) (hb : d150025 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d52069, d150025, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d52069, d150025, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h18 (q : Pattern) (ha : d52070 q = 1) (hb : d150026 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d52070, d150026, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d52070, d150026, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h19 (q : Pattern) (ha : d52071 q = 1) (hb : d150027 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d52071, d150027, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d52071, d150027, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h20 (q : Pattern) (ha : d52072 q = 1) (hb : d150028 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d52072, d150028, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d52072, d150028, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h21 (q : Pattern) (ha : d52073 q = 1) (hb : d150029 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d52073, d150029, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d52073, d150029, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
  exact h21 p ha hb
theorem andIntro48731 (p : Pattern) (ha : d20966 p = 1) (hb : d52083 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d20906 q = 1) (hb : d52008 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d20906, d52008, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48721 q ha hb
    | true =>
      simp only [d20906, d52008, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5 q ha hb
  have h2 (q : Pattern) (ha : d20962 q = 1) (hb : d52079 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d20962, d52079, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20962, d52079, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d20963 q = 1) (hb : d52080 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d20963, d52080, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d20963, d52080, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d20964 q = 1) (hb : d52081 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d20964, d52081, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20964, d52081, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d20965 q = 1) (hb : d52082 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d20965, d52082, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20965, d52082, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d20966 q = 1) (hb : d52083 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d20966, d52083, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20966, d52083, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro48732 (p : Pattern) (ha : d20973 p = 1) (hb : d52090 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d20906 q = 1) (hb : d52008 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d20906, d52008, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48721 q ha hb
    | true =>
      simp only [d20906, d52008, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5 q ha hb
  have h2 (q : Pattern) (ha : d20962 q = 1) (hb : d52079 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d20962, d52079, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20962, d52079, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d20963 q = 1) (hb : d52080 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d20963, d52080, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d20963, d52080, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d20964 q = 1) (hb : d52081 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d20964, d52081, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20964, d52081, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d20965 q = 1) (hb : d52082 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d20965, d52082, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20965, d52082, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d20913 q = 1) (hb : d52024 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d20913, d52024, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48723 q ha hb
    | true =>
      simp only [d20913, d52024, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7 q ha hb
  have h7 (q : Pattern) (ha : d20969 q = 1) (hb : d52086 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d20969, d52086, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20969, d52086, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d20970 q = 1) (hb : d52087 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d20970, d52087, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d20970, d52087, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d20971 q = 1) (hb : d52088 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d20971, d52088, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20971, d52088, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d20972 q = 1) (hb : d52089 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d20972, d52089, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20972, d52089, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d20973 q = 1) (hb : d52090 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d20973, d52090, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d20973, d52090, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro48733 (p : Pattern) (ha : d21058 p = 1) (hb : d52163 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d20906 q = 1) (hb : d52008 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d20906, d52008, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48721 q ha hb
    | true =>
      simp only [d20906, d52008, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5 q ha hb
  have h2 (q : Pattern) (ha : d20962 q = 1) (hb : d52079 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d20962, d52079, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20962, d52079, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d20963 q = 1) (hb : d52080 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d20963, d52080, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d20963, d52080, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d20964 q = 1) (hb : d52081 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d20964, d52081, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20964, d52081, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d20965 q = 1) (hb : d52082 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d20965, d52082, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20965, d52082, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d43 q = 1) (hb : d51895 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d43, d51895, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5 q ha hb
    | true =>
      simp only [d43, d51895, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d100 q = 1) (hb : d51952 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d100, d51952, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d100, d51952, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d101 q = 1) (hb : d51953 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d101, d51953, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d101, d51953, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d102 q = 1) (hb : d51954 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d102, d51954, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d102, d51954, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d103 q = 1) (hb : d51955 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d103, d51955, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d103, d51955, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d21058 q = 1) (hb : d52163 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d21058, d52163, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d21058, d52163, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro48734 (p : Pattern) (ha : d20978 p = 1) (hb : d52095 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d20900 q = 1) (hb : d52002 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d20900, d52002, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48720 q ha hb
    | true =>
      simp only [d20900, d52002, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d20901 q = 1) (hb : d52003 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d20901, d52003, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20901, d52003, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d37 q = 1) (hb : d51889 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d37, d51889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4 q ha hb
    | true =>
      simp only [d37, d51889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d38 q = 1) (hb : d51890 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d38, d51890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d38, d51890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d20902 q = 1) (hb : d52004 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d20902, d52004, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d20902, d52004, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d20903 q = 1) (hb : d52005 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d20903, d52005, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d20903, d52005, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d20977 q = 1) (hb : d52094 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d20977, d52094, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20977, d52094, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d20978 q = 1) (hb : d52095 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d20978, d52095, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20978, d52095, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro48735 (p : Pattern) (ha : d20985 p = 1) (hb : d52102 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d20900 q = 1) (hb : d52002 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d20900, d52002, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48720 q ha hb
    | true =>
      simp only [d20900, d52002, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d20901 q = 1) (hb : d52003 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d20901, d52003, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20901, d52003, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d37 q = 1) (hb : d51889 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d37, d51889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4 q ha hb
    | true =>
      simp only [d37, d51889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d38 q = 1) (hb : d51890 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d38, d51890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d38, d51890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d20902 q = 1) (hb : d52004 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d20902, d52004, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d20902, d52004, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d20983 q = 1) (hb : d52100 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d20983, d52100, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20983, d52100, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d20984 q = 1) (hb : d52101 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d20984, d52101, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d20984, d52101, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d20985 q = 1) (hb : d52102 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d20985, d52102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20985, d52102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro48736 (p : Pattern) (ha : d20996 p = 1) (hb : d126874 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d20990 q = 1) (hb : d52118 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d20990, d52118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46036 q ha hb
    | true =>
      simp only [d20990, d52118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d20991 q = 1) (hb : d52119 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d20991, d52119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d20991, d52119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d20992 q = 1) (hb : d52120 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d20992, d52120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20992, d52120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d20993 q = 1) (hb : d52121 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d20993, d52121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d20993, d52121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d751 q = 1) (hb : d51990 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d751, d51990, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33341 q ha hb
    | true =>
      simp only [d751, d51990, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d752 q = 1) (hb : d51991 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d752, d51991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d752, d51991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d753 q = 1) (hb : d51992 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d753, d51992, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d753, d51992, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d754 q = 1) (hb : d51993 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d754, d51993, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d754, d51993, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d20994 q = 1) (hb : d52122 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d20994, d52122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d20994, d52122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d5451 q = 1) (hb : d101015 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d5451, d101015, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46070 q ha hb
    | true =>
      simp only [d5451, d101015, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d5452 q = 1) (hb : d101017 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d5452, d101017, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d5452, d101017, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d5453 q = 1) (hb : d112927 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d5453, d112927, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d5453, d112927, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d5454 q = 1) (hb : d112928 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d5454, d112928, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d5454, d112928, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d25 q = 1) (hb : d51877 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d25, d51877, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro2 q ha hb
    | true =>
      simp only [d25, d51877, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d26 q = 1) (hb : d51878 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d26, d51878, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d26, d51878, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h16 (q : Pattern) (ha : d27 q = 1) (hb : d51879 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d27, d51879, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d27, d51879, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d28 q = 1) (hb : d51880 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d28, d51880, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d28, d51880, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h18 (q : Pattern) (ha : d20995 q = 1) (hb : d112929 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d20995, d112929, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d20995, d112929, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d20996 q = 1) (hb : d126874 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d20996, d126874, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d20996, d126874, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro48737 (p : Pattern) (ha : d21002 p = 1) (hb : d126880 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d20997 q = 1) (hb : d126875 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d20997, d126875, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48736 q ha hb
    | true =>
      simp only [d20997, d126875, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48719 q ha hb
  have h2 (q : Pattern) (ha : d20998 q = 1) (hb : d126876 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d20998, d126876, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20998, d126876, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d20999 q = 1) (hb : d126877 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d20999, d126877, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20999, d126877, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d20894 q = 1) (hb : d51996 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d20894, d51996, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48719 q ha hb
    | true =>
      simp only [d20894, d51996, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro3 q ha hb
  have h5 (q : Pattern) (ha : d20895 q = 1) (hb : d51997 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d20895, d51997, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20895, d51997, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d20896 q = 1) (hb : d51998 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d20896, d51998, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20896, d51998, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d21000 q = 1) (hb : d126878 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d21000, d126878, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d21000, d126878, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d31 q = 1) (hb : d51883 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d31, d51883, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro3 q ha hb
    | true =>
      simp only [d31, d51883, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d32 q = 1) (hb : d51884 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d32, d51884, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d32, d51884, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d33 q = 1) (hb : d51885 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d33, d51885, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d33, d51885, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d20897 q = 1) (hb : d51999 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d20897, d51999, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d20897, d51999, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d21001 q = 1) (hb : d126879 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d21001, d126879, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d21001, d126879, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d21002 q = 1) (hb : d126880 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d21002, d126880, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d21002, d126880, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h13 p ha hb
theorem andIntro48738 (p : Pattern) (ha : d21008 p = 1) (hb : d126886 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d21003 q = 1) (hb : d126881 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d21003, d126881, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48737 q ha hb
    | true =>
      simp only [d21003, d126881, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d21004 q = 1) (hb : d126882 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d21004, d126882, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21004, d126882, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d20900 q = 1) (hb : d52002 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d20900, d52002, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48720 q ha hb
    | true =>
      simp only [d20900, d52002, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d20901 q = 1) (hb : d52003 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d20901, d52003, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20901, d52003, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d21005 q = 1) (hb : d126883 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d21005, d126883, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d21005, d126883, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d21006 q = 1) (hb : d126884 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d21006, d126884, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d21006, d126884, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d21007 q = 1) (hb : d126885 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d21007, d126885, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d21007, d126885, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d21008 q = 1) (hb : d126886 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d21008, d126886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21008, d126886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro48739 (p : Pattern) (ha : d21029 p = 1) (hb : d68835 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d20900 q = 1) (hb : d52002 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d20900, d52002, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48720 q ha hb
    | true =>
      simp only [d20900, d52002, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d20901 q = 1) (hb : d52003 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d20901, d52003, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20901, d52003, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d21026 q = 1) (hb : d68832 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d21026, d68832, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d21026, d68832, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d21027 q = 1) (hb : d68833 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d21027, d68833, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d21027, d68833, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d21028 q = 1) (hb : d68834 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d21028, d68834, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d21028, d68834, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d21029 q = 1) (hb : d68835 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d21029, d68835, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21029, d68835, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro48740 (p : Pattern) (ha : d126892 p = 1) (hb : d150039 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d20979 q = 1) (hb : d52096 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d20979, d52096, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48734 q ha hb
    | true =>
      simp only [d20979, d52096, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28 q ha hb
  have h2 (q : Pattern) (ha : d20980 q = 1) (hb : d52097 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d20980, d52097, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20980, d52097, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d20981 q = 1) (hb : d52098 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d20981, d52098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d20981, d52098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d20982 q = 1) (hb : d52099 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d20982, d52099, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20982, d52099, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d20986 q = 1) (hb : d52103 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d20986, d52103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48735 q ha hb
    | true =>
      simp only [d20986, d52103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29 q ha hb
  have h6 (q : Pattern) (ha : d20987 q = 1) (hb : d52104 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d20987, d52104, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20987, d52104, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d20988 q = 1) (hb : d52105 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d20988, d52105, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d20988, d52105, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d21009 q = 1) (hb : d126887 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d21009, d126887, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48738 q ha hb
    | true =>
      simp only [d21009, d126887, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48721 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d52008 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d126888 q = 1) (hb : d150035 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d126888, d150035, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
    | true =>
      simp only [d126888, d150035, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
  have h11 (q : Pattern) (ha : d21030 q = 1) (hb : d68836 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d21030, d68836, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48739 q ha hb
    | true =>
      simp only [d21030, d68836, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d21031 q = 1) (hb : d74076 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d21031, d74076, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d21031, d74076, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d126889 q = 1) (hb : d150036 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d126889, d150036, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d126889, d150036, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
  have h14 (q : Pattern) (ha : d126890 q = 1) (hb : d150037 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d126890, d150037, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
    | true =>
      simp only [d126890, d150037, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d126891 q = 1) (hb : d150038 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d126891, d150038, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d126891, d150038, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d126892 q = 1) (hb : d150039 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d126892, d150039, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d126892, d150039, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  exact h16 p ha hb
theorem andIntro48741 (p : Pattern) (ha : d21036 p = 1) (hb : d52144 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d20900 q = 1) (hb : d52002 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d20900, d52002, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48720 q ha hb
    | true =>
      simp only [d20900, d52002, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d20901 q = 1) (hb : d52003 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d20901, d52003, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20901, d52003, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d37 q = 1) (hb : d51889 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d37, d51889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4 q ha hb
    | true =>
      simp only [d37, d51889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d38 q = 1) (hb : d51890 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d38, d51890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d38, d51890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d20902 q = 1) (hb : d52004 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d20902, d52004, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d20902, d52004, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d20903 q = 1) (hb : d52005 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d20903, d52005, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d20903, d52005, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d20977 q = 1) (hb : d52094 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d20977, d52094, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20977, d52094, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d21036 q = 1) (hb : d52144 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d21036, d52144, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d21036, d52144, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro48742 (p : Pattern) (ha : d21041 p = 1) (hb : d52149 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d20900 q = 1) (hb : d52002 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d20900, d52002, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48720 q ha hb
    | true =>
      simp only [d20900, d52002, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d20901 q = 1) (hb : d52003 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d20901, d52003, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20901, d52003, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d37 q = 1) (hb : d51889 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d37, d51889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4 q ha hb
    | true =>
      simp only [d37, d51889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d38 q = 1) (hb : d51890 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d38, d51890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d38, d51890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d20902 q = 1) (hb : d52004 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d20902, d52004, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d20902, d52004, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d20983 q = 1) (hb : d52100 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d20983, d52100, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20983, d52100, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d20984 q = 1) (hb : d52101 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d20984, d52101, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d20984, d52101, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d21041 q = 1) (hb : d52149 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d21041, d52149, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d21041, d52149, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro48743 (p : Pattern) (ha : d21045 p = 1) (hb : d126893 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d21003 q = 1) (hb : d126881 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d21003, d126881, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48737 q ha hb
    | true =>
      simp only [d21003, d126881, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d21004 q = 1) (hb : d126882 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d21004, d126882, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21004, d126882, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d20900 q = 1) (hb : d52002 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d20900, d52002, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48720 q ha hb
    | true =>
      simp only [d20900, d52002, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d20901 q = 1) (hb : d52003 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d20901, d52003, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20901, d52003, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d21005 q = 1) (hb : d126883 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d21005, d126883, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d21005, d126883, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d21006 q = 1) (hb : d126884 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d21006, d126884, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d21006, d126884, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d21007 q = 1) (hb : d126885 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d21007, d126885, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d21007, d126885, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d21045 q = 1) (hb : d126893 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d21045, d126893, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d21045, d126893, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro48744 (p : Pattern) (ha : d21050 p = 1) (hb : d74081 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d20900 q = 1) (hb : d52002 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d20900, d52002, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48720 q ha hb
    | true =>
      simp only [d20900, d52002, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d20901 q = 1) (hb : d52003 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d20901, d52003, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20901, d52003, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d21026 q = 1) (hb : d68832 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d21026, d68832, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d21026, d68832, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d21027 q = 1) (hb : d68833 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d21027, d68833, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d21027, d68833, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d21028 q = 1) (hb : d68834 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d21028, d68834, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d21028, d68834, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d21050 q = 1) (hb : d74081 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d21050, d74081, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d21050, d74081, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro48745 (p : Pattern) (ha : d126899 p = 1) (hb : d150044 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d20979 q = 1) (hb : d52096 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d20979, d52096, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48734 q ha hb
    | true =>
      simp only [d20979, d52096, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28 q ha hb
  have h2 (q : Pattern) (ha : d20980 q = 1) (hb : d52097 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d20980, d52097, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20980, d52097, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d20981 q = 1) (hb : d52098 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d20981, d52098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d20981, d52098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d20982 q = 1) (hb : d52099 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d20982, d52099, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20982, d52099, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d20986 q = 1) (hb : d52103 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d20986, d52103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48735 q ha hb
    | true =>
      simp only [d20986, d52103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29 q ha hb
  have h6 (q : Pattern) (ha : d20987 q = 1) (hb : d52104 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d20987, d52104, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20987, d52104, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d20988 q = 1) (hb : d52105 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d20988, d52105, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d20988, d52105, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d21009 q = 1) (hb : d126887 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d21009, d126887, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48738 q ha hb
    | true =>
      simp only [d21009, d126887, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48721 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d52008 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d126888 q = 1) (hb : d150035 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d126888, d150035, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
    | true =>
      simp only [d126888, d150035, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
  have h11 (q : Pattern) (ha : d21030 q = 1) (hb : d68836 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d21030, d68836, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48739 q ha hb
    | true =>
      simp only [d21030, d68836, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d21031 q = 1) (hb : d74076 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d21031, d74076, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d21031, d74076, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d126889 q = 1) (hb : d150036 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d126889, d150036, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d126889, d150036, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
  have h14 (q : Pattern) (ha : d126890 q = 1) (hb : d150037 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d126890, d150037, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
    | true =>
      simp only [d126890, d150037, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d126891 q = 1) (hb : d150038 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d126891, d150038, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d126891, d150038, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d21037 q = 1) (hb : d52145 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d21037, d52145, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48741 q ha hb
    | true =>
      simp only [d21037, d52145, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32 q ha hb
  have h17 (q : Pattern) (ha : d21038 q = 1) (hb : d52146 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d21038, d52146, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21038, d52146, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d21039 q = 1) (hb : d52147 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d21039, d52147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d21039, d52147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h19 (q : Pattern) (ha : d21040 q = 1) (hb : d52148 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d21040, d52148, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21040, d52148, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d21042 q = 1) (hb : d52150 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d21042, d52150, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48742 q ha hb
    | true =>
      simp only [d21042, d52150, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33 q ha hb
  have h21 (q : Pattern) (ha : d21043 q = 1) (hb : d52151 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d21043, d52151, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21043, d52151, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
  have h22 (q : Pattern) (ha : d21044 q = 1) (hb : d52152 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d21044, d52152, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d21044, d52152, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h23 (q : Pattern) (ha : d21046 q = 1) (hb : d126894 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d21046, d126894, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48743 q ha hb
    | true =>
      simp only [d21046, d126894, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48723 q ha hb
  have h24 (q : Pattern) (ha : d0 q = 1) (hb : d52024 q = 1) : d0 q = 1 := by
    exact ha
  have h25 (q : Pattern) (ha : d126895 q = 1) (hb : d150040 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d126895, d150040, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q hb ha
    | true =>
      simp only [d126895, d150040, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q hb ha
  have h26 (q : Pattern) (ha : d21051 q = 1) (hb : d74082 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d21051, d74082, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48744 q ha hb
    | true =>
      simp only [d21051, d74082, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h27 (q : Pattern) (ha : d21052 q = 1) (hb : d74083 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d21052, d74083, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h26 q ha hb
    | true =>
      simp only [d21052, d74083, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h28 (q : Pattern) (ha : d126896 q = 1) (hb : d150041 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d126896, d150041, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q ha hb
    | true =>
      simp only [d126896, d150041, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h27 q hb ha
  have h29 (q : Pattern) (ha : d126897 q = 1) (hb : d150042 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d126897, d150042, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q hb ha
    | true =>
      simp only [d126897, d150042, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h28 q ha hb
  have h30 (q : Pattern) (ha : d126898 q = 1) (hb : d150043 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d126898, d150043, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q hb ha
    | true =>
      simp only [d126898, d150043, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h29 q ha hb
  have h31 (q : Pattern) (ha : d126899 q = 1) (hb : d150044 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d126899, d150044, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d126899, d150044, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h30 q ha hb
  exact h31 p ha hb
theorem andIntro48746 (p : Pattern) (ha : d126906 p = 1) (hb : d150051 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d21046 q = 1) (hb : d126894 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d21046, d126894, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48743 q ha hb
    | true =>
      simp only [d21046, d126894, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48723 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d52024 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d126895 q = 1) (hb : d150040 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d126895, d150040, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d126895, d150040, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d21051 q = 1) (hb : d74082 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d21051, d74082, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48744 q ha hb
    | true =>
      simp only [d21051, d74082, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d21052 q = 1) (hb : d74083 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d21052, d74083, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d21052, d74083, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d126896 q = 1) (hb : d150041 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d126896, d150041, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d126896, d150041, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d126904 q = 1) (hb : d150049 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d126904, d150049, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d126904, d150049, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d126905 q = 1) (hb : d150050 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d126905, d150050, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d126905, d150050, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d126906 q = 1) (hb : d150051 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d126906, d150051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d126906, d150051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro48747 (p : Pattern) (ha : d21077 p = 1) (hb : d126912 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d21071 q = 1) (hb : d52178 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d21071, d52178, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21071, d52178, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46036 q ha hb
  have h2 (q : Pattern) (ha : d20990 q = 1) (hb : d52118 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d20990, d52118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46036 q ha hb
    | true =>
      simp only [d20990, d52118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d21072 q = 1) (hb : d52179 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d21072, d52179, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d21072, d52179, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d20991 q = 1) (hb : d52119 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d20991, d52119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d20991, d52119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d21073 q = 1) (hb : d52180 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d21073, d52180, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d21073, d52180, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d21074 q = 1) (hb : d52181 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d21074, d52181, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d21074, d52181, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d971 q = 1) (hb : d52044 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d971, d52044, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d971, d52044, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33341 q ha hb
  have h8 (q : Pattern) (ha : d751 q = 1) (hb : d51990 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d751, d51990, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33341 q ha hb
    | true =>
      simp only [d751, d51990, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d972 q = 1) (hb : d52045 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d972, d52045, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d972, d52045, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d752 q = 1) (hb : d51991 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d752, d51991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d752, d51991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d973 q = 1) (hb : d52046 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d973, d52046, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d973, d52046, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d974 q = 1) (hb : d52047 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d974, d52047, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d974, d52047, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d21075 q = 1) (hb : d52182 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d21075, d52182, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d21075, d52182, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d5495 q = 1) (hb : d113007 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d5495, d113007, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d5495, d113007, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46070 q ha hb
  have h15 (q : Pattern) (ha : d5451 q = 1) (hb : d101015 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d5451, d101015, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46070 q ha hb
    | true =>
      simp only [d5451, d101015, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h16 (q : Pattern) (ha : d5496 q = 1) (hb : d113008 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d5496, d113008, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d5496, d113008, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d5452 q = 1) (hb : d101017 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d5452, d101017, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d5452, d101017, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h18 (q : Pattern) (ha : d5497 q = 1) (hb : d113009 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d5497, d113009, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d5497, d113009, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d5498 q = 1) (hb : d113010 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d5498, d113010, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d5498, d113010, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h20 (q : Pattern) (ha : d66 q = 1) (hb : d51918 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d66, d51918, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d66, d51918, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro2 q ha hb
  have h21 (q : Pattern) (ha : d25 q = 1) (hb : d51877 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d25, d51877, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro2 q ha hb
    | true =>
      simp only [d25, d51877, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h22 (q : Pattern) (ha : d67 q = 1) (hb : d51919 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d67, d51919, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d67, d51919, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
  have h23 (q : Pattern) (ha : d26 q = 1) (hb : d51878 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d26, d51878, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d26, d51878, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h24 (q : Pattern) (ha : d68 q = 1) (hb : d51920 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d68, d51920, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
    | true =>
      simp only [d68, d51920, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
  have h25 (q : Pattern) (ha : d69 q = 1) (hb : d51921 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d69, d51921, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q ha hb
    | true =>
      simp only [d69, d51921, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h26 (q : Pattern) (ha : d21076 q = 1) (hb : d113011 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d21076, d113011, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d21076, d113011, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q ha hb
  have h27 (q : Pattern) (ha : d21077 q = 1) (hb : d126912 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d21077, d126912, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d21077, d126912, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h26 q ha hb
  exact h27 p ha hb
theorem andIntro48748 (p : Pattern) (ha : d21083 p = 1) (hb : d126918 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d21078 q = 1) (hb : d126913 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d21078, d126913, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48747 q ha hb
    | true =>
      simp only [d21078, d126913, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48726 q ha hb
  have h2 (q : Pattern) (ha : d21079 q = 1) (hb : d126914 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d21079, d126914, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21079, d126914, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d21080 q = 1) (hb : d126915 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d21080, d126915, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21080, d126915, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d20933 q = 1) (hb : d52050 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d20933, d52050, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48726 q ha hb
    | true =>
      simp only [d20933, d52050, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10 q ha hb
  have h5 (q : Pattern) (ha : d20934 q = 1) (hb : d52051 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d20934, d52051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20934, d52051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d20935 q = 1) (hb : d52052 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d20935, d52052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20935, d52052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d21081 q = 1) (hb : d126916 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d21081, d126916, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d21081, d126916, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d72 q = 1) (hb : d51924 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d72, d51924, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10 q ha hb
    | true =>
      simp only [d72, d51924, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d73 q = 1) (hb : d51925 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d73, d51925, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d73, d51925, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d74 q = 1) (hb : d51926 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d74, d51926, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d74, d51926, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d20936 q = 1) (hb : d52053 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d20936, d52053, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d20936, d52053, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d21082 q = 1) (hb : d126917 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d21082, d126917, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d21082, d126917, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d21083 q = 1) (hb : d126918 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d21083, d126918, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d21083, d126918, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h13 p ha hb
theorem andIntro48749 (p : Pattern) (ha : d21089 p = 1) (hb : d126924 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d21084 q = 1) (hb : d126919 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d21084, d126919, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48748 q ha hb
    | true =>
      simp only [d21084, d126919, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d21085 q = 1) (hb : d126920 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d21085, d126920, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21085, d126920, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d20939 q = 1) (hb : d52056 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d20939, d52056, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48727 q ha hb
    | true =>
      simp only [d20939, d52056, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d20940 q = 1) (hb : d52057 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d20940, d52057, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20940, d52057, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d21086 q = 1) (hb : d126921 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d21086, d126921, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d21086, d126921, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d21087 q = 1) (hb : d126922 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d21087, d126922, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d21087, d126922, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d21088 q = 1) (hb : d126923 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d21088, d126923, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d21088, d126923, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d21089 q = 1) (hb : d126924 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d21089, d126924, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d21089, d126924, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
end NetHack.Soko22Hazard87
