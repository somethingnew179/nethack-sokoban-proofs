import NetHack.Soko22Hazard87.AndIntroBlocks0069
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Soko22Hazard87
open NetHack.Sokoban NetHack.Sokoban.PatternCorrection
theorem andIntro17500 (p : Pattern) (ha : d8149 p = 1) (hb : d92315 p = 1) : d112393 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d92315 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d8140 q = 1) (hb : d92315 q = 1) : d112388 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d8140, d112388, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17498 q ha hb
    | true =>
      simp only [d8140, d112388, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d8141 q = 1) (hb : d92315 q = 1) : d112389 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d8141, d112389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8141, d112389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d8144 q = 1) (hb : d92315 q = 1) : d99125 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d8144, d99125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17499 q ha hb
    | true =>
      simp only [d8144, d99125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d8145 q = 1) (hb : d92315 q = 1) : d99126 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d8145, d99126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8145, d99126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d8146 q = 1) (hb : d92315 q = 1) : d112390 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d8146, d112390, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d8146, d112390, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d8147 q = 1) (hb : d92315 q = 1) : d112391 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d8147, d112391, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d8147, d112391, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d8148 q = 1) (hb : d92315 q = 1) : d112392 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d8148, d112392, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d8148, d112392, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d8149 q = 1) (hb : d92315 q = 1) : d112393 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d8149, d112393, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d8149, d112393, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro17501 (p : Pattern) (ha : d8153 p = 1) (hb : d92315 p = 1) : d112397 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d92315 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d8144 q = 1) (hb : d92315 q = 1) : d99125 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d8144, d99125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17499 q ha hb
    | true =>
      simp only [d8144, d99125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d8145 q = 1) (hb : d92315 q = 1) : d99126 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d8145, d99126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8145, d99126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d2387 q = 1) (hb : d92315 q = 1) : d2387 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d8150 q = 1) (hb : d92315 q = 1) : d112394 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d8150, d112394, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d8150, d112394, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d8151 q = 1) (hb : d92315 q = 1) : d112395 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d8151, d112395, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d8151, d112395, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d8152 q = 1) (hb : d92315 q = 1) : d112396 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d8152, d112396, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d8152, d112396, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d8153 q = 1) (hb : d92315 q = 1) : d112397 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d8153, d112397, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d8153, d112397, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h7 p ha hb
theorem andIntro17502 (p : Pattern) (ha : d8168 p = 1) (hb : d92315 p = 1) : d112403 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d92315 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d8144 q = 1) (hb : d92315 q = 1) : d99125 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d8144, d99125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17499 q ha hb
    | true =>
      simp only [d8144, d99125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d8145 q = 1) (hb : d92315 q = 1) : d99126 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d8145, d99126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8145, d99126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d8165 q = 1) (hb : d92315 q = 1) : d112400 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d8165, d112400, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d8165, d112400, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d8166 q = 1) (hb : d92315 q = 1) : d112401 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d8166, d112401, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d8166, d112401, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d8167 q = 1) (hb : d92315 q = 1) : d112402 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d8167, d112402, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d8167, d112402, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d8168 q = 1) (hb : d92315 q = 1) : d112403 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d8168, d112403, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d8168, d112403, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro17503 (p : Pattern) (ha : d85659 p = 1) (hb : d92315 p = 1) : d112409 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d92315 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d8154 q = 1) (hb : d92315 q = 1) : d112398 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d8154, d112398, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17500 q ha hb
    | true =>
      simp only [d8154, d112398, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17501 q ha hb
  have h2 (q : Pattern) (ha : d85655 q = 1) (hb : d92315 q = 1) : d112399 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d85655, d112399, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d85655, d112399, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d8169 q = 1) (hb : d92315 q = 1) : d112404 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d8169, d112404, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17502 q ha hb
    | true =>
      simp only [d8169, d112404, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d8170 q = 1) (hb : d92315 q = 1) : d112405 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d8170, d112405, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d8170, d112405, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d85656 q = 1) (hb : d92315 q = 1) : d112406 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d85656, d112406, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d85656, d112406, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d85657 q = 1) (hb : d92315 q = 1) : d112407 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d85657, d112407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d85657, d112407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d85658 q = 1) (hb : d92315 q = 1) : d112408 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d85658, d112408, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d85658, d112408, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d85659 q = 1) (hb : d92315 q = 1) : d112409 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d85659, d112409, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d85659, d112409, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro17504 (p : Pattern) (ha : d85665 p = 1) (hb : d92315 p = 1) : d112415 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d92315 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d8050 q = 1) (hb : d92315 q = 1) : d112309 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d8050, d112309, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8050, d112309, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17482 q ha hb
  have h2 (q : Pattern) (ha : d8051 q = 1) (hb : d92315 q = 1) : d112310 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d8051, d112310, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d8051, d112310, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d8059 q = 1) (hb : d92315 q = 1) : d112318 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d8059, d112318, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17482 q ha hb
    | true =>
      simp only [d8059, d112318, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17484 q ha hb
  have h4 (q : Pattern) (ha : d8060 q = 1) (hb : d92315 q = 1) : d112319 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d8060, d112319, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d8060, d112319, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d8061 q = 1) (hb : d92315 q = 1) : d112320 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d8061, d112320, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d8061, d112320, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d85643 q = 1) (hb : d92315 q = 1) : d112372 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d85643, d112372, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17491 q ha hb
    | true =>
      simp only [d85643, d112372, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17496 q ha hb
  have h7 (q : Pattern) (ha : d2316 q = 1) (hb : d92315 q = 1) : d2316 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d8126 q = 1) (hb : d92315 q = 1) : d112374 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d8126, d112374, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17485 q ha hb
    | true =>
      simp only [d8126, d112374, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d85644 q = 1) (hb : d92315 q = 1) : d112375 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d85644, d112375, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d85644, d112375, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d85645 q = 1) (hb : d92315 q = 1) : d112376 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d85645, d112376, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d85645, d112376, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d85646 q = 1) (hb : d92315 q = 1) : d112377 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d85646, d112377, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d85646, d112377, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d85650 q = 1) (hb : d92315 q = 1) : d112381 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d85650, d112381, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d85650, d112381, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17497 q ha hb
  have h13 (q : Pattern) (ha : d2326 q = 1) (hb : d92315 q = 1) : d2326 q = 1 := by
    exact ha
  have h14 (q : Pattern) (ha : d85651 q = 1) (hb : d92315 q = 1) : d112382 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d85651, d112382, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d85651, d112382, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d85652 q = 1) (hb : d92315 q = 1) : d112383 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d85652, d112383, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d85652, d112383, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h16 (q : Pattern) (ha : d85653 q = 1) (hb : d92315 q = 1) : d112384 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d85653, d112384, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d85653, d112384, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h17 (q : Pattern) (ha : d85654 q = 1) (hb : d92315 q = 1) : d112385 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d85654, d112385, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d85654, d112385, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d85660 q = 1) (hb : d92315 q = 1) : d112410 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d85660, d112410, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d85660, d112410, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17503 q ha hb
  have h19 (q : Pattern) (ha : d2459 q = 1) (hb : d92315 q = 1) : d2459 q = 1 := by
    exact ha
  have h20 (q : Pattern) (ha : d85661 q = 1) (hb : d92315 q = 1) : d112411 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d85661, d112411, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d85661, d112411, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
  have h21 (q : Pattern) (ha : d85662 q = 1) (hb : d92315 q = 1) : d112412 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d85662, d112412, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d85662, d112412, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h22 (q : Pattern) (ha : d85663 q = 1) (hb : d92315 q = 1) : d112413 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d85663, d112413, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d85663, d112413, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h23 (q : Pattern) (ha : d85664 q = 1) (hb : d92315 q = 1) : d112414 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d85664, d112414, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
    | true =>
      simp only [d85664, d112414, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h24 (q : Pattern) (ha : d85665 q = 1) (hb : d92315 q = 1) : d112415 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d85665, d112415, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d85665, d112415, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
  exact h24 p ha hb
theorem andIntro17505 (p : Pattern) (ha : d85671 p = 1) (hb : d92315 p = 1) : d112421 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d92315 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d85666 q = 1) (hb : d92315 q = 1) : d112416 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d85666, d112416, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d85666, d112416, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17504 q ha hb
  have h2 (q : Pattern) (ha : d85667 q = 1) (hb : d92315 q = 1) : d112417 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d85667, d112417, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d85667, d112417, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d85668 q = 1) (hb : d92315 q = 1) : d112418 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d85668, d112418, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d85668, d112418, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d85669 q = 1) (hb : d92315 q = 1) : d112419 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d85669, d112419, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d85669, d112419, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d85670 q = 1) (hb : d92315 q = 1) : d112420 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d85670, d112420, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d85670, d112420, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d85671 q = 1) (hb : d92315 q = 1) : d112421 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d85671, d112421, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d85671, d112421, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro17506 (p : Pattern) (ha : d85677 p = 1) (hb : d92315 p = 1) : d112427 p = 1 := by
  have h0 (q : Pattern) (ha : d85506 q = 1) (hb : d92315 q = 1) : d111920 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d85506, d111920, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17377 q ha hb
    | true =>
      simp only [d85506, d111920, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17401 q ha hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d92315 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d85546 q = 1) (hb : d92315 q = 1) : d112044 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d85546, d112044, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d85546, d112044, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17427 q ha hb
  have h3 (q : Pattern) (ha : d85547 q = 1) (hb : d92315 q = 1) : d112045 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d85547, d112045, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d85547, d112045, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d85587 q = 1) (hb : d92315 q = 1) : d112169 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d85587, d112169, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d85587, d112169, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17453 q ha hb
  have h5 (q : Pattern) (ha : d85588 q = 1) (hb : d92315 q = 1) : d112170 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d85588, d112170, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d85588, d112170, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d85589 q = 1) (hb : d92315 q = 1) : d112171 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d85589, d112171, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d85589, d112171, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d85629 q = 1) (hb : d92315 q = 1) : d112295 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d85629, d112295, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d85629, d112295, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17479 q ha hb
  have h8 (q : Pattern) (ha : d85630 q = 1) (hb : d92315 q = 1) : d112296 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d85630, d112296, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d85630, d112296, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d85631 q = 1) (hb : d92315 q = 1) : d112297 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d85631, d112297, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d85631, d112297, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d85632 q = 1) (hb : d92315 q = 1) : d112298 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d85632, d112298, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d85632, d112298, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d85672 q = 1) (hb : d92315 q = 1) : d112422 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d85672, d112422, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d85672, d112422, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17505 q ha hb
  have h12 (q : Pattern) (ha : d85673 q = 1) (hb : d92315 q = 1) : d112423 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d85673, d112423, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d85673, d112423, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d85674 q = 1) (hb : d92315 q = 1) : d112424 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d85674, d112424, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d85674, d112424, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d85675 q = 1) (hb : d92315 q = 1) : d112425 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d85675, d112425, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d85675, d112425, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d85676 q = 1) (hb : d92315 q = 1) : d112426 q = 1 := by
    cases bit : q 10250 with
    | false =>
      simp only [d85676, d112426, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d85676, d112426, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d85677 q = 1) (hb : d92315 q = 1) : d112427 q = 1 := by
    cases bit : q 260 with
    | false =>
      simp only [d85677, d112427, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d85677, d112427, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  exact h16 p ha hb
theorem andIntro17507 (p : Pattern) (ha : d85683 p = 1) (hb : d92315 p = 1) : d112433 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d92315 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d85678 q = 1) (hb : d92315 q = 1) : d112428 q = 1 := by
    cases bit : q 259 with
    | false =>
      simp only [d85678, d112428, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17506 q ha hb
    | true =>
      simp only [d85678, d112428, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d85679 q = 1) (hb : d92315 q = 1) : d112429 q = 1 := by
    cases bit : q 258 with
    | false =>
      simp only [d85679, d112429, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d85679, d112429, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d85680 q = 1) (hb : d92315 q = 1) : d112430 q = 1 := by
    cases bit : q 257 with
    | false =>
      simp only [d85680, d112430, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d85680, d112430, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d85681 q = 1) (hb : d92315 q = 1) : d112431 q = 1 := by
    cases bit : q 256 with
    | false =>
      simp only [d85681, d112431, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d85681, d112431, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d85682 q = 1) (hb : d92315 q = 1) : d112432 q = 1 := by
    cases bit : q 255 with
    | false =>
      simp only [d85682, d112432, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d85682, d112432, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d85683 q = 1) (hb : d92315 q = 1) : d112433 q = 1 := by
    cases bit : q 254 with
    | false =>
      simp only [d85683, d112433, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d85683, d112433, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro17508 (p : Pattern) (ha : d85689 p = 1) (hb : d92315 p = 1) : d112439 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d92315 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d85684 q = 1) (hb : d92315 q = 1) : d112434 q = 1 := by
    cases bit : q 253 with
    | false =>
      simp only [d85684, d112434, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17507 q ha hb
    | true =>
      simp only [d85684, d112434, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d85685 q = 1) (hb : d92315 q = 1) : d112435 q = 1 := by
    cases bit : q 252 with
    | false =>
      simp only [d85685, d112435, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d85685, d112435, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d85686 q = 1) (hb : d92315 q = 1) : d112436 q = 1 := by
    cases bit : q 251 with
    | false =>
      simp only [d85686, d112436, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d85686, d112436, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d85687 q = 1) (hb : d92315 q = 1) : d112437 q = 1 := by
    cases bit : q 250 with
    | false =>
      simp only [d85687, d112437, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d85687, d112437, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d85688 q = 1) (hb : d92315 q = 1) : d112438 q = 1 := by
    cases bit : q 249 with
    | false =>
      simp only [d85688, d112438, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d85688, d112438, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d85689 q = 1) (hb : d92315 q = 1) : d112439 q = 1 := by
    cases bit : q 245 with
    | false =>
      simp only [d85689, d112439, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d85689, d112439, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro17509 (p : Pattern) (ha : d85695 p = 1) (hb : d92315 p = 1) : d112445 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d92315 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d85690 q = 1) (hb : d92315 q = 1) : d112440 q = 1 := by
    cases bit : q 200 with
    | false =>
      simp only [d85690, d112440, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17508 q ha hb
    | true =>
      simp only [d85690, d112440, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d85691 q = 1) (hb : d92315 q = 1) : d112441 q = 1 := by
    cases bit : q 199 with
    | false =>
      simp only [d85691, d112441, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d85691, d112441, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d85692 q = 1) (hb : d92315 q = 1) : d112442 q = 1 := by
    cases bit : q 186 with
    | false =>
      simp only [d85692, d112442, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d85692, d112442, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d85693 q = 1) (hb : d92315 q = 1) : d112443 q = 1 := by
    cases bit : q 185 with
    | false =>
      simp only [d85693, d112443, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d85693, d112443, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d85694 q = 1) (hb : d92315 q = 1) : d112444 q = 1 := by
    cases bit : q 184 with
    | false =>
      simp only [d85694, d112444, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d85694, d112444, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d85695 q = 1) (hb : d92315 q = 1) : d112445 q = 1 := by
    cases bit : q 181 with
    | false =>
      simp only [d85695, d112445, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d85695, d112445, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro17510 (p : Pattern) (ha : d85701 p = 1) (hb : d92315 p = 1) : d112451 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d92315 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d85696 q = 1) (hb : d92315 q = 1) : d112446 q = 1 := by
    cases bit : q 177 with
    | false =>
      simp only [d85696, d112446, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17509 q ha hb
    | true =>
      simp only [d85696, d112446, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d85697 q = 1) (hb : d92315 q = 1) : d112447 q = 1 := by
    cases bit : q 164 with
    | false =>
      simp only [d85697, d112447, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d85697, d112447, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d85698 q = 1) (hb : d92315 q = 1) : d112448 q = 1 := by
    cases bit : q 156 with
    | false =>
      simp only [d85698, d112448, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d85698, d112448, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d85699 q = 1) (hb : d92315 q = 1) : d112449 q = 1 := by
    cases bit : q 155 with
    | false =>
      simp only [d85699, d112449, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d85699, d112449, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d85700 q = 1) (hb : d92315 q = 1) : d112450 q = 1 := by
    cases bit : q 134 with
    | false =>
      simp only [d85700, d112450, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d85700, d112450, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d85701 q = 1) (hb : d92315 q = 1) : d112451 q = 1 := by
    cases bit : q 133 with
    | false =>
      simp only [d85701, d112451, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d85701, d112451, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro17511 (p : Pattern) (ha : d85707 p = 1) (hb : d92315 p = 1) : d112457 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d92315 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d85702 q = 1) (hb : d92315 q = 1) : d112452 q = 1 := by
    cases bit : q 120 with
    | false =>
      simp only [d85702, d112452, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17510 q ha hb
    | true =>
      simp only [d85702, d112452, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d85703 q = 1) (hb : d92315 q = 1) : d112453 q = 1 := by
    cases bit : q 118 with
    | false =>
      simp only [d85703, d112453, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d85703, d112453, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d85704 q = 1) (hb : d92315 q = 1) : d112454 q = 1 := by
    cases bit : q 114 with
    | false =>
      simp only [d85704, d112454, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d85704, d112454, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d85705 q = 1) (hb : d92315 q = 1) : d112455 q = 1 := by
    cases bit : q 111 with
    | false =>
      simp only [d85705, d112455, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d85705, d112455, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d85706 q = 1) (hb : d92315 q = 1) : d112456 q = 1 := by
    cases bit : q 98 with
    | false =>
      simp only [d85706, d112456, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d85706, d112456, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d85707 q = 1) (hb : d92315 q = 1) : d112457 q = 1 := by
    cases bit : q 97 with
    | false =>
      simp only [d85707, d112457, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d85707, d112457, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro17512 (p : Pattern) (ha : d85713 p = 1) (hb : d92315 p = 1) : d112463 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d92315 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d85708 q = 1) (hb : d92315 q = 1) : d112458 q = 1 := by
    cases bit : q 94 with
    | false =>
      simp only [d85708, d112458, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17511 q ha hb
    | true =>
      simp only [d85708, d112458, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d85709 q = 1) (hb : d92315 q = 1) : d112459 q = 1 := by
    cases bit : q 76 with
    | false =>
      simp only [d85709, d112459, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d85709, d112459, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d85710 q = 1) (hb : d92315 q = 1) : d112460 q = 1 := by
    cases bit : q 67 with
    | false =>
      simp only [d85710, d112460, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d85710, d112460, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d85711 q = 1) (hb : d92315 q = 1) : d112461 q = 1 := by
    cases bit : q 52 with
    | false =>
      simp only [d85711, d112461, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d85711, d112461, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d85712 q = 1) (hb : d92315 q = 1) : d112462 q = 1 := by
    cases bit : q 47 with
    | false =>
      simp only [d85712, d112462, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d85712, d112462, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d85713 q = 1) (hb : d92315 q = 1) : d112463 q = 1 := by
    cases bit : q 46 with
    | false =>
      simp only [d85713, d112463, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d85713, d112463, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro17513 (p : Pattern) (ha : d85719 p = 1) (hb : d92315 p = 1) : d112469 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d92315 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d85714 q = 1) (hb : d92315 q = 1) : d112464 q = 1 := by
    cases bit : q 45 with
    | false =>
      simp only [d85714, d112464, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17512 q ha hb
    | true =>
      simp only [d85714, d112464, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d85715 q = 1) (hb : d92315 q = 1) : d112465 q = 1 := by
    cases bit : q 30 with
    | false =>
      simp only [d85715, d112465, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d85715, d112465, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d85716 q = 1) (hb : d92315 q = 1) : d112466 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d85716, d112466, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d85716, d112466, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d85717 q = 1) (hb : d92315 q = 1) : d112467 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d85717, d112467, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d85717, d112467, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d85718 q = 1) (hb : d92315 q = 1) : d112468 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d85718, d112468, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d85718, d112468, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d85719 q = 1) (hb : d92315 q = 1) : d112469 q = 1 := by
    cases bit : q 25 with
    | false =>
      simp only [d85719, d112469, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d85719, d112469, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro17514 (p : Pattern) (ha : d481 p = 1) (hb : d81527 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d145 q = 1) (hb : d51996 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d145, d51996, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20 q ha hb
    | true =>
      simp only [d145, d51996, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro3 q ha hb
  have h2 (q : Pattern) (ha : d146 q = 1) (hb : d51997 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d146, d51997, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d146, d51997, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d147 q = 1) (hb : d51998 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d147, d51998, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d147, d51998, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d475 q = 1) (hb : d52222 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d475, d52222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d475, d52222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d51886 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d480 q = 1) (hb : d81526 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d480, d81526, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d480, d81526, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d481 q = 1) (hb : d81527 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d481, d81527, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d481, d81527, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h7 p ha hb
theorem andIntro17515 (p : Pattern) (ha : d92321 p = 1) (hb : d111667 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d482 q = 1) (hb : d81528 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d482, d81528, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17514 q ha hb
    | true =>
      simp only [d482, d81528, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d483 q = 1) (hb : d81529 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d483, d81529, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d483, d81529, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
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
  have h5 (q : Pattern) (ha : d92318 q = 1) (hb : d111664 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d92318, d111664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d92318, d111664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d92319 q = 1) (hb : d111665 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d92319, d111665, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d92319, d111665, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d92320 q = 1) (hb : d111666 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d92320, d111666, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d92320, d111666, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d92321 q = 1) (hb : d111667 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d92321, d111667, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92321, d111667, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro17516 (p : Pattern) (ha : d92327 p = 1) (hb : d111673 p = 1) : d0 p = 1 := by
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
  have h8 (q : Pattern) (ha : d92322 q = 1) (hb : d111668 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d92322, d111668, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17515 q ha hb
    | true =>
      simp only [d92322, d111668, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5 q hb ha
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d51895 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d92323 q = 1) (hb : d111669 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d92323, d111669, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d92323, d111669, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
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
  have h13 (q : Pattern) (ha : d92324 q = 1) (hb : d111670 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d92324, d111670, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d92324, d111670, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
  have h14 (q : Pattern) (ha : d92325 q = 1) (hb : d111671 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d92325, d111671, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
    | true =>
      simp only [d92325, d111671, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d92326 q = 1) (hb : d111672 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d92326, d111672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d92326, d111672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d92327 q = 1) (hb : d111673 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d92327, d111673, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92327, d111673, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  exact h16 p ha hb
theorem andIntro17517 (p : Pattern) (ha : d92328 p = 1) (hb : d111674 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d482 q = 1) (hb : d81528 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d482, d81528, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17514 q ha hb
    | true =>
      simp only [d482, d81528, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d483 q = 1) (hb : d81529 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d483, d81529, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d483, d81529, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
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
  have h5 (q : Pattern) (ha : d92318 q = 1) (hb : d111664 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d92318, d111664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d92318, d111664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d92319 q = 1) (hb : d111665 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d92319, d111665, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d92319, d111665, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d92320 q = 1) (hb : d111666 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d92320, d111666, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d92320, d111666, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d92328 q = 1) (hb : d111674 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d92328, d111674, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d92328, d111674, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro17518 (p : Pattern) (ha : d92334 p = 1) (hb : d111680 p = 1) : d0 p = 1 := by
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
  have h8 (q : Pattern) (ha : d92322 q = 1) (hb : d111668 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d92322, d111668, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17515 q ha hb
    | true =>
      simp only [d92322, d111668, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5 q hb ha
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d51895 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d92323 q = 1) (hb : d111669 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d92323, d111669, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d92323, d111669, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
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
  have h13 (q : Pattern) (ha : d92324 q = 1) (hb : d111670 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d92324, d111670, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d92324, d111670, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
  have h14 (q : Pattern) (ha : d92325 q = 1) (hb : d111671 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d92325, d111671, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
    | true =>
      simp only [d92325, d111671, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d92326 q = 1) (hb : d111672 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d92326, d111672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d92326, d111672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
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
  have h23 (q : Pattern) (ha : d92329 q = 1) (hb : d111675 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d92329, d111675, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17517 q ha hb
    | true =>
      simp only [d92329, d111675, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7 q hb ha
  have h24 (q : Pattern) (ha : d0 q = 1) (hb : d51902 q = 1) : d0 q = 1 := by
    exact ha
  have h25 (q : Pattern) (ha : d92330 q = 1) (hb : d111676 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d92330, d111676, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
    | true =>
      simp only [d92330, d111676, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
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
  have h28 (q : Pattern) (ha : d92331 q = 1) (hb : d111677 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d92331, d111677, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q ha hb
    | true =>
      simp only [d92331, d111677, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h27 q hb ha
  have h29 (q : Pattern) (ha : d92332 q = 1) (hb : d111678 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d92332, d111678, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q hb ha
    | true =>
      simp only [d92332, d111678, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h28 q ha hb
  have h30 (q : Pattern) (ha : d92333 q = 1) (hb : d111679 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d92333, d111679, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q hb ha
    | true =>
      simp only [d92333, d111679, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h29 q ha hb
  have h31 (q : Pattern) (ha : d92334 q = 1) (hb : d111680 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d92334, d111680, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d92334, d111680, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h30 q ha hb
  exact h31 p ha hb
theorem andIntro17519 (p : Pattern) (ha : d92341 p = 1) (hb : d111687 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d92329 q = 1) (hb : d111675 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d92329, d111675, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17517 q ha hb
    | true =>
      simp only [d92329, d111675, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7 q hb ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d51902 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d92330 q = 1) (hb : d111676 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d92330, d111676, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d92330, d111676, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
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
  have h6 (q : Pattern) (ha : d92331 q = 1) (hb : d111677 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d92331, d111677, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d92331, d111677, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d92339 q = 1) (hb : d111685 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d92339, d111685, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92339, d111685, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d92340 q = 1) (hb : d111686 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d92340, d111686, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92340, d111686, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d92341 q = 1) (hb : d111687 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d92341, d111687, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92341, d111687, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro17520 (p : Pattern) (ha : d683 p = 1) (hb : d81560 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d232 q = 1) (hb : d52050 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d232, d52050, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24 q ha hb
    | true =>
      simp only [d232, d52050, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10 q ha hb
  have h2 (q : Pattern) (ha : d233 q = 1) (hb : d52051 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d233, d52051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d233, d52051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d234 q = 1) (hb : d52052 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d234, d52052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d234, d52052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d673 q = 1) (hb : d52377 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d673, d52377, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d673, d52377, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d51927 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d682 q = 1) (hb : d81559 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d682, d81559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d682, d81559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d683 q = 1) (hb : d81560 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d683, d81560, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d683, d81560, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h7 p ha hb
theorem andIntro17521 (p : Pattern) (ha : d92350 p = 1) (hb : d111696 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d684 q = 1) (hb : d81561 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d684, d81561, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17520 q ha hb
    | true =>
      simp only [d684, d81561, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d685 q = 1) (hb : d81562 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d685, d81562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d685, d81562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
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
  have h5 (q : Pattern) (ha : d92347 q = 1) (hb : d111693 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d92347, d111693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d92347, d111693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d92348 q = 1) (hb : d111694 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d92348, d111694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d92348, d111694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d92349 q = 1) (hb : d111695 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d92349, d111695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d92349, d111695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d92350 q = 1) (hb : d111696 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d92350, d111696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d92350, d111696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro17522 (p : Pattern) (ha : d92356 p = 1) (hb : d111702 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d92351 q = 1) (hb : d111697 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d92351, d111697, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17521 q ha hb
    | true =>
      simp only [d92351, d111697, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12 q hb ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d51936 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d92352 q = 1) (hb : d111698 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d92352, d111698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d92352, d111698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
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
  have h6 (q : Pattern) (ha : d92353 q = 1) (hb : d111699 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d92353, d111699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d92353, d111699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d92354 q = 1) (hb : d111700 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d92354, d111700, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92354, d111700, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d92355 q = 1) (hb : d111701 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d92355, d111701, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92355, d111701, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d92356 q = 1) (hb : d111702 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d92356, d111702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92356, d111702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro17523 (p : Pattern) (ha : d92362 p = 1) (hb : d111708 p = 1) : d0 p = 1 := by
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
  have h6 (q : Pattern) (ha : d92335 q = 1) (hb : d111681 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d92335, d111681, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17516 q ha hb
    | true =>
      simp only [d92335, d111681, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17518 q ha hb
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
  have h8 (q : Pattern) (ha : d92336 q = 1) (hb : d111682 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d92336, d111682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d92336, d111682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
  have h9 (q : Pattern) (ha : d92337 q = 1) (hb : d111683 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d92337, d111683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d92337, d111683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h10 (q : Pattern) (ha : d92338 q = 1) (hb : d111684 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d92338, d111684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
    | true =>
      simp only [d92338, d111684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d92342 q = 1) (hb : d111688 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d92342, d111688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92342, d111688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17519 q ha hb
  have h12 (q : Pattern) (ha : d92343 q = 1) (hb : d111689 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d92343, d111689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d92343, d111689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d92344 q = 1) (hb : d111690 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d92344, d111690, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d92344, d111690, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h14 (q : Pattern) (ha : d92345 q = 1) (hb : d111691 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d92345, d111691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d92345, d111691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h15 (q : Pattern) (ha : d92346 q = 1) (hb : d111692 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d92346, d111692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d92346, d111692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d92357 q = 1) (hb : d111703 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d92357, d111703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92357, d111703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17522 q ha hb
  have h17 (q : Pattern) (ha : d92358 q = 1) (hb : d111704 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d92358, d111704, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d92358, d111704, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h18 (q : Pattern) (ha : d92359 q = 1) (hb : d111705 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d92359, d111705, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d92359, d111705, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h19 (q : Pattern) (ha : d92360 q = 1) (hb : d111706 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d92360, d111706, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d92360, d111706, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h20 (q : Pattern) (ha : d92361 q = 1) (hb : d111707 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d92361, d111707, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d92361, d111707, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h21 (q : Pattern) (ha : d92362 q = 1) (hb : d111708 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d92362, d111708, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d92362, d111708, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
  exact h21 p ha hb
theorem andIntro17524 (p : Pattern) (ha : d92372 p = 1) (hb : d111718 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d92322 q = 1) (hb : d111668 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d92322, d111668, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17515 q ha hb
    | true =>
      simp only [d92322, d111668, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5 q hb ha
  have h2 (q : Pattern) (ha : d92368 q = 1) (hb : d111714 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d92368, d111714, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92368, d111714, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d92369 q = 1) (hb : d111715 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d92369, d111715, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d92369, d111715, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d92370 q = 1) (hb : d111716 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d92370, d111716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92370, d111716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d92371 q = 1) (hb : d111717 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d92371, d111717, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92371, d111717, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d92372 q = 1) (hb : d111718 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d92372, d111718, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92372, d111718, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro17525 (p : Pattern) (ha : d92379 p = 1) (hb : d111725 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d92322 q = 1) (hb : d111668 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d92322, d111668, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17515 q ha hb
    | true =>
      simp only [d92322, d111668, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5 q hb ha
  have h2 (q : Pattern) (ha : d92368 q = 1) (hb : d111714 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d92368, d111714, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92368, d111714, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d92369 q = 1) (hb : d111715 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d92369, d111715, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d92369, d111715, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d92370 q = 1) (hb : d111716 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d92370, d111716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92370, d111716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d92371 q = 1) (hb : d111717 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d92371, d111717, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92371, d111717, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d92329 q = 1) (hb : d111675 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d92329, d111675, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17517 q ha hb
    | true =>
      simp only [d92329, d111675, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7 q hb ha
  have h7 (q : Pattern) (ha : d92375 q = 1) (hb : d111721 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d92375, d111721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92375, d111721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d92376 q = 1) (hb : d111722 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d92376, d111722, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d92376, d111722, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d92377 q = 1) (hb : d111723 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d92377, d111723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92377, d111723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d92378 q = 1) (hb : d111724 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d92378, d111724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92378, d111724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d92379 q = 1) (hb : d111725 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d92379, d111725, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d92379, d111725, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro17526 (p : Pattern) (ha : d491 p = 1) (hb : d92408 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d482 q = 1) (hb : d81528 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d482, d81528, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17514 q ha hb
    | true =>
      simp only [d482, d81528, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d483 q = 1) (hb : d81529 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d483, d81529, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d483, d81529, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d488 q = 1) (hb : d92405 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d488, d92405, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d488, d92405, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d489 q = 1) (hb : d92406 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d489, d92406, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d489, d92406, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d490 q = 1) (hb : d92407 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d490, d92407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d490, d92407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d491 q = 1) (hb : d92408 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d491, d92408, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d491, d92408, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro17527 (p : Pattern) (ha : d92384 p = 1) (hb : d111730 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d482 q = 1) (hb : d81528 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d482, d81528, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17514 q ha hb
    | true =>
      simp only [d482, d81528, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d483 q = 1) (hb : d81529 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d483, d81529, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d483, d81529, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
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
  have h5 (q : Pattern) (ha : d92318 q = 1) (hb : d111664 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d92318, d111664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d92318, d111664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d92319 q = 1) (hb : d111665 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d92319, d111665, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d92319, d111665, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d92383 q = 1) (hb : d111729 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d92383, d111729, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92383, d111729, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d92384 q = 1) (hb : d111730 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d92384, d111730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92384, d111730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro17528 (p : Pattern) (ha : d92391 p = 1) (hb : d111737 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d482 q = 1) (hb : d81528 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d482, d81528, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17514 q ha hb
    | true =>
      simp only [d482, d81528, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d483 q = 1) (hb : d81529 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d483, d81529, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d483, d81529, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
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
  have h5 (q : Pattern) (ha : d92318 q = 1) (hb : d111664 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d92318, d111664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d92318, d111664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d92389 q = 1) (hb : d111735 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d92389, d111735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92389, d111735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d92390 q = 1) (hb : d111736 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d92390, d111736, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d92390, d111736, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d92391 q = 1) (hb : d111737 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d92391, d111737, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92391, d111737, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro17529 (p : Pattern) (ha : d92396 p = 1) (hb : d98845 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d325 q = 1) (hb : d52124 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d325, d52124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43 q ha hb
    | true =>
      simp only [d325, d52124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20 q ha hb
  have h2 (q : Pattern) (ha : d326 q = 1) (hb : d52125 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d326, d52125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d326, d52125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d327 q = 1) (hb : d52126 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d327, d52126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d327, d52126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d6797 q = 1) (hb : d81585 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d6797, d81585, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d6797, d81585, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d52222 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d92395 q = 1) (hb : d98844 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d92395, d98844, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d92395, d98844, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d92396 q = 1) (hb : d98845 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d92396, d98845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d92396, d98845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h7 p ha hb
theorem andIntro17530 (p : Pattern) (ha : d92402 p = 1) (hb : d111744 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d92397 q = 1) (hb : d98846 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d92397, d98846, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17529 q ha hb
    | true =>
      simp only [d92397, d98846, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d92398 q = 1) (hb : d98847 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d92398, d98847, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92398, d98847, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d482 q = 1) (hb : d81528 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d482, d81528, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17514 q ha hb
    | true =>
      simp only [d482, d81528, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d483 q = 1) (hb : d81529 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d483, d81529, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d483, d81529, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d92399 q = 1) (hb : d111741 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d92399, d111741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d92399, d111741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d92400 q = 1) (hb : d111742 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d92400, d111742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d92400, d111742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d92401 q = 1) (hb : d111743 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d92401, d111743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d92401, d111743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d92402 q = 1) (hb : d111744 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d92402, d111744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92402, d111744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro17531 (p : Pattern) (ha : d92414 p = 1) (hb : d111751 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d92385 q = 1) (hb : d111731 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d92385, d111731, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17527 q ha hb
    | true =>
      simp only [d92385, d111731, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28 q hb ha
  have h2 (q : Pattern) (ha : d92386 q = 1) (hb : d111732 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d92386, d111732, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92386, d111732, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d92387 q = 1) (hb : d111733 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d92387, d111733, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d92387, d111733, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d92388 q = 1) (hb : d111734 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d92388, d111734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92388, d111734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d92392 q = 1) (hb : d111738 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d92392, d111738, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17528 q ha hb
    | true =>
      simp only [d92392, d111738, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29 q hb ha
  have h6 (q : Pattern) (ha : d92393 q = 1) (hb : d111739 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d92393, d111739, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92393, d111739, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d92394 q = 1) (hb : d111740 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d92394, d111740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d92394, d111740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d92403 q = 1) (hb : d111745 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d92403, d111745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17530 q ha hb
    | true =>
      simp only [d92403, d111745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17515 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d92322 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d92404 q = 1) (hb : d111746 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d92404, d111746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d92404, d111746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
  have h11 (q : Pattern) (ha : d633 q = 1) (hb : d92409 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d633, d92409, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17526 q ha hb
    | true =>
      simp only [d633, d92409, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d92410 q = 1) (hb : d111747 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d92410, d111747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
    | true =>
      simp only [d92410, d111747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d92411 q = 1) (hb : d111748 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d92411, d111748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d92411, d111748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d92412 q = 1) (hb : d111749 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d92412, d111749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d92412, d111749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d92413 q = 1) (hb : d111750 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d92413, d111750, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d92413, d111750, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d92414 q = 1) (hb : d111751 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d92414, d111751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92414, d111751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  exact h16 p ha hb
theorem andIntro17532 (p : Pattern) (ha : d501 p = 1) (hb : d92427 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d482 q = 1) (hb : d81528 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d482, d81528, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17514 q ha hb
    | true =>
      simp only [d482, d81528, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d483 q = 1) (hb : d81529 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d483, d81529, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d483, d81529, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d488 q = 1) (hb : d92405 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d488, d92405, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d488, d92405, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d489 q = 1) (hb : d92406 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d489, d92406, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d489, d92406, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d490 q = 1) (hb : d92407 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d490, d92407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d490, d92407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d501 q = 1) (hb : d92427 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d501, d92427, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d501, d92427, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro17533 (p : Pattern) (ha : d92415 p = 1) (hb : d111752 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d482 q = 1) (hb : d81528 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d482, d81528, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17514 q ha hb
    | true =>
      simp only [d482, d81528, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d483 q = 1) (hb : d81529 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d483, d81529, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d483, d81529, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
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
  have h5 (q : Pattern) (ha : d92318 q = 1) (hb : d111664 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d92318, d111664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d92318, d111664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d92319 q = 1) (hb : d111665 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d92319, d111665, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d92319, d111665, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d92383 q = 1) (hb : d111729 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d92383, d111729, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92383, d111729, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d92415 q = 1) (hb : d111752 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d92415, d111752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d92415, d111752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro17534 (p : Pattern) (ha : d92420 p = 1) (hb : d111757 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d482 q = 1) (hb : d81528 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d482, d81528, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17514 q ha hb
    | true =>
      simp only [d482, d81528, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d483 q = 1) (hb : d81529 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d483, d81529, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d483, d81529, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
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
  have h5 (q : Pattern) (ha : d92318 q = 1) (hb : d111664 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d92318, d111664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d92318, d111664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d92389 q = 1) (hb : d111735 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d92389, d111735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92389, d111735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d92390 q = 1) (hb : d111736 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d92390, d111736, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d92390, d111736, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d92420 q = 1) (hb : d111757 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d92420, d111757, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d92420, d111757, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro17535 (p : Pattern) (ha : d92424 p = 1) (hb : d111761 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d92397 q = 1) (hb : d98846 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d92397, d98846, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17529 q ha hb
    | true =>
      simp only [d92397, d98846, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d92398 q = 1) (hb : d98847 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d92398, d98847, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92398, d98847, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d482 q = 1) (hb : d81528 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d482, d81528, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17514 q ha hb
    | true =>
      simp only [d482, d81528, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d483 q = 1) (hb : d81529 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d483, d81529, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d483, d81529, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d92399 q = 1) (hb : d111741 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d92399, d111741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d92399, d111741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d92400 q = 1) (hb : d111742 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d92400, d111742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d92400, d111742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d92401 q = 1) (hb : d111743 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d92401, d111743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d92401, d111743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d92424 q = 1) (hb : d111761 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d92424, d111761, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d92424, d111761, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro17536 (p : Pattern) (ha : d92433 p = 1) (hb : d111768 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d92385 q = 1) (hb : d111731 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d92385, d111731, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17527 q ha hb
    | true =>
      simp only [d92385, d111731, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28 q hb ha
  have h2 (q : Pattern) (ha : d92386 q = 1) (hb : d111732 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d92386, d111732, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92386, d111732, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d92387 q = 1) (hb : d111733 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d92387, d111733, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d92387, d111733, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d92388 q = 1) (hb : d111734 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d92388, d111734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92388, d111734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d92392 q = 1) (hb : d111738 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d92392, d111738, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17528 q ha hb
    | true =>
      simp only [d92392, d111738, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29 q hb ha
  have h6 (q : Pattern) (ha : d92393 q = 1) (hb : d111739 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d92393, d111739, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92393, d111739, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d92394 q = 1) (hb : d111740 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d92394, d111740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d92394, d111740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d92403 q = 1) (hb : d111745 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d92403, d111745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17530 q ha hb
    | true =>
      simp only [d92403, d111745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17515 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d92322 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d92404 q = 1) (hb : d111746 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d92404, d111746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d92404, d111746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
  have h11 (q : Pattern) (ha : d633 q = 1) (hb : d92409 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d633, d92409, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17526 q ha hb
    | true =>
      simp only [d633, d92409, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d92410 q = 1) (hb : d111747 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d92410, d111747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
    | true =>
      simp only [d92410, d111747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d92411 q = 1) (hb : d111748 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d92411, d111748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d92411, d111748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d92412 q = 1) (hb : d111749 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d92412, d111749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d92412, d111749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d92413 q = 1) (hb : d111750 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d92413, d111750, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d92413, d111750, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d92416 q = 1) (hb : d111753 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d92416, d111753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17533 q ha hb
    | true =>
      simp only [d92416, d111753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32 q hb ha
  have h17 (q : Pattern) (ha : d92417 q = 1) (hb : d111754 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d92417, d111754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92417, d111754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d92418 q = 1) (hb : d111755 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d92418, d111755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d92418, d111755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h19 (q : Pattern) (ha : d92419 q = 1) (hb : d111756 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d92419, d111756, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92419, d111756, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d92421 q = 1) (hb : d111758 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d92421, d111758, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17534 q ha hb
    | true =>
      simp only [d92421, d111758, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33 q hb ha
  have h21 (q : Pattern) (ha : d92422 q = 1) (hb : d111759 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d92422, d111759, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92422, d111759, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
  have h22 (q : Pattern) (ha : d92423 q = 1) (hb : d111760 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d92423, d111760, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d92423, d111760, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h23 (q : Pattern) (ha : d92425 q = 1) (hb : d111762 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d92425, d111762, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17535 q ha hb
    | true =>
      simp only [d92425, d111762, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17517 q ha hb
  have h24 (q : Pattern) (ha : d0 q = 1) (hb : d92329 q = 1) : d0 q = 1 := by
    exact ha
  have h25 (q : Pattern) (ha : d92426 q = 1) (hb : d111763 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d92426, d111763, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
    | true =>
      simp only [d92426, d111763, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q hb ha
  have h26 (q : Pattern) (ha : d639 q = 1) (hb : d92428 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d639, d92428, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17532 q ha hb
    | true =>
      simp only [d639, d92428, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h27 (q : Pattern) (ha : d92429 q = 1) (hb : d111764 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d92429, d111764, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h26 q hb ha
    | true =>
      simp only [d92429, d111764, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h28 (q : Pattern) (ha : d92430 q = 1) (hb : d111765 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d92430, d111765, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q ha hb
    | true =>
      simp only [d92430, d111765, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h27 q ha hb
  have h29 (q : Pattern) (ha : d92431 q = 1) (hb : d111766 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d92431, d111766, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
    | true =>
      simp only [d92431, d111766, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h28 q ha hb
  have h30 (q : Pattern) (ha : d92432 q = 1) (hb : d111767 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d92432, d111767, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d92432, d111767, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h29 q ha hb
  have h31 (q : Pattern) (ha : d92433 q = 1) (hb : d111768 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d92433, d111768, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d92433, d111768, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h30 q ha hb
  exact h31 p ha hb
theorem andIntro17537 (p : Pattern) (ha : d92435 p = 1) (hb : d111770 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d92322 q = 1) (hb : d111668 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d92322, d111668, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17515 q ha hb
    | true =>
      simp only [d92322, d111668, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5 q hb ha
  have h2 (q : Pattern) (ha : d92368 q = 1) (hb : d111714 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d92368, d111714, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92368, d111714, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d92369 q = 1) (hb : d111715 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d92369, d111715, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d92369, d111715, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d92370 q = 1) (hb : d111716 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d92370, d111716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92370, d111716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d92371 q = 1) (hb : d111717 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d92371, d111717, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92371, d111717, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
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
  have h11 (q : Pattern) (ha : d92435 q = 1) (hb : d111770 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d92435, d111770, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d92435, d111770, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
  exact h11 p ha hb
theorem andIntro17538 (p : Pattern) (ha : d92442 p = 1) (hb : d111777 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d92425 q = 1) (hb : d111762 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d92425, d111762, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17535 q ha hb
    | true =>
      simp only [d92425, d111762, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17517 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d92329 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d92426 q = 1) (hb : d111763 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d92426, d111763, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d92426, d111763, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d639 q = 1) (hb : d92428 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d639, d92428, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17532 q ha hb
    | true =>
      simp only [d639, d92428, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d92429 q = 1) (hb : d111764 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d92429, d111764, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d92429, d111764, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d92430 q = 1) (hb : d111765 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d92430, d111765, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d92430, d111765, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d92440 q = 1) (hb : d111775 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d92440, d111775, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92440, d111775, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d92441 q = 1) (hb : d111776 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d92441, d111776, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92441, d111776, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d92442 q = 1) (hb : d111777 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d92442, d111777, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92442, d111777, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro17539 (p : Pattern) (ha : d730 p = 1) (hb : d92461 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d684 q = 1) (hb : d81561 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d684, d81561, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17520 q ha hb
    | true =>
      simp only [d684, d81561, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d685 q = 1) (hb : d81562 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d685, d81562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d685, d81562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d727 q = 1) (hb : d92458 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d727, d92458, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d727, d92458, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d728 q = 1) (hb : d92459 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d728, d92459, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d728, d92459, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d729 q = 1) (hb : d92460 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d729, d92460, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d729, d92460, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d730 q = 1) (hb : d92461 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d730, d92461, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d730, d92461, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro17540 (p : Pattern) (ha : d92449 p = 1) (hb : d98878 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d418 q = 1) (hb : d52184 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d418, d52184, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47 q ha hb
    | true =>
      simp only [d418, d52184, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24 q ha hb
  have h2 (q : Pattern) (ha : d419 q = 1) (hb : d52185 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d419, d52185, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d419, d52185, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d420 q = 1) (hb : d52186 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d420, d52186, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d420, d52186, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d6843 q = 1) (hb : d81631 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d6843, d81631, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d6843, d81631, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d52377 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d92448 q = 1) (hb : d98877 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d92448, d98877, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d92448, d98877, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d92449 q = 1) (hb : d98878 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d92449, d98878, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d92449, d98878, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h7 p ha hb
theorem andIntro17541 (p : Pattern) (ha : d92455 p = 1) (hb : d111786 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d92450 q = 1) (hb : d98879 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d92450, d98879, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17540 q ha hb
    | true =>
      simp only [d92450, d98879, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d92451 q = 1) (hb : d98880 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d92451, d98880, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92451, d98880, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d684 q = 1) (hb : d81561 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d684, d81561, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17520 q ha hb
    | true =>
      simp only [d684, d81561, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d685 q = 1) (hb : d81562 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d685, d81562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d685, d81562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d92452 q = 1) (hb : d111783 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d92452, d111783, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d92452, d111783, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d92453 q = 1) (hb : d111784 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d92453, d111784, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d92453, d111784, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d92454 q = 1) (hb : d111785 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d92454, d111785, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d92454, d111785, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d92455 q = 1) (hb : d111786 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d92455, d111786, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d92455, d111786, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro17542 (p : Pattern) (ha : d92467 p = 1) (hb : d111793 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d92456 q = 1) (hb : d111787 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d92456, d111787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17541 q ha hb
    | true =>
      simp only [d92456, d111787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17521 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d92351 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d92457 q = 1) (hb : d111788 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d92457, d111788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d92457, d111788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d731 q = 1) (hb : d92462 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d731, d92462, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17539 q ha hb
    | true =>
      simp only [d731, d92462, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d92463 q = 1) (hb : d111789 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d92463, d111789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d92463, d111789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d92464 q = 1) (hb : d111790 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d92464, d111790, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d92464, d111790, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d92465 q = 1) (hb : d111791 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d92465, d111791, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92465, d111791, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d92466 q = 1) (hb : d111792 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d92466, d111792, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92466, d111792, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d92467 q = 1) (hb : d111793 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d92467, d111793, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92467, d111793, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro17543 (p : Pattern) (ha : d92473 p = 1) (hb : d111799 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d92373 q = 1) (hb : d111719 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d92373, d111719, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92373, d111719, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17524 q ha hb
  have h2 (q : Pattern) (ha : d92374 q = 1) (hb : d111720 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d92374, d111720, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d92374, d111720, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d92380 q = 1) (hb : d111726 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d92380, d111726, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17524 q ha hb
    | true =>
      simp only [d92380, d111726, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17525 q ha hb
  have h4 (q : Pattern) (ha : d92381 q = 1) (hb : d111727 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d92381, d111727, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d92381, d111727, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d92382 q = 1) (hb : d111728 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d92382, d111728, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d92382, d111728, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d92434 q = 1) (hb : d111769 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d92434, d111769, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17531 q ha hb
    | true =>
      simp only [d92434, d111769, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17536 q ha hb
  have h7 (q : Pattern) (ha : d92436 q = 1) (hb : d111771 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d92436, d111771, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17537 q ha hb
    | true =>
      simp only [d92436, d111771, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16 q hb ha
  have h8 (q : Pattern) (ha : d92437 q = 1) (hb : d111772 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d92437, d111772, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d92437, d111772, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d92438 q = 1) (hb : d111773 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d92438, d111773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d92438, d111773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h10 (q : Pattern) (ha : d92439 q = 1) (hb : d111774 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d92439, d111774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d92439, d111774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d92443 q = 1) (hb : d111778 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d92443, d111778, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92443, d111778, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17538 q ha hb
  have h12 (q : Pattern) (ha : d407 q = 1) (hb : d52173 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d407, d52173, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d407, d52173, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39 q ha hb
  have h13 (q : Pattern) (ha : d92444 q = 1) (hb : d111779 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d92444, d111779, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d92444, d111779, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
  have h14 (q : Pattern) (ha : d92445 q = 1) (hb : d111780 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d92445, d111780, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d92445, d111780, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h15 (q : Pattern) (ha : d92446 q = 1) (hb : d111781 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d92446, d111781, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d92446, d111781, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h16 (q : Pattern) (ha : d92447 q = 1) (hb : d111782 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d92447, d111782, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d92447, d111782, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d92468 q = 1) (hb : d111794 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d92468, d111794, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92468, d111794, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17542 q ha hb
  have h18 (q : Pattern) (ha : d463 q = 1) (hb : d52210 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d463, d52210, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d463, d52210, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40 q ha hb
  have h19 (q : Pattern) (ha : d92469 q = 1) (hb : d111795 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d92469, d111795, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d92469, d111795, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q hb ha
  have h20 (q : Pattern) (ha : d92470 q = 1) (hb : d111796 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d92470, d111796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d92470, d111796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h21 (q : Pattern) (ha : d92471 q = 1) (hb : d111797 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d92471, d111797, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d92471, d111797, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h22 (q : Pattern) (ha : d92472 q = 1) (hb : d111798 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d92472, d111798, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d92472, d111798, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h23 (q : Pattern) (ha : d92473 q = 1) (hb : d111799 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d92473, d111799, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d92473, d111799, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
  exact h23 p ha hb
theorem andIntro17544 (p : Pattern) (ha : d92479 p = 1) (hb : d111805 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d96 q = 1) (hb : d51948 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d96, d51948, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d96, d51948, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro14 q ha hb
  have h2 (q : Pattern) (ha : d97 q = 1) (hb : d51949 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d97, d51949, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d97, d51949, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d98 q = 1) (hb : d51950 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d98, d51950, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d98, d51950, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d99 q = 1) (hb : d51951 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d99, d51951, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d99, d51951, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d92363 q = 1) (hb : d111709 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d92363, d111709, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92363, d111709, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17523 q ha hb
  have h6 (q : Pattern) (ha : d92364 q = 1) (hb : d111710 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d92364, d111710, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92364, d111710, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d92365 q = 1) (hb : d111711 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d92365, d111711, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92365, d111711, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d92366 q = 1) (hb : d111712 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d92366, d111712, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92366, d111712, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d92367 q = 1) (hb : d111713 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d92367, d111713, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d92367, d111713, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d92474 q = 1) (hb : d111800 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d92474, d111800, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92474, d111800, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17543 q ha hb
  have h11 (q : Pattern) (ha : d92475 q = 1) (hb : d111801 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d92475, d111801, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92475, d111801, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d92476 q = 1) (hb : d111802 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d92476, d111802, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92476, d111802, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d92477 q = 1) (hb : d111803 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d92477, d111803, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92477, d111803, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d92478 q = 1) (hb : d111804 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d92478, d111804, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92478, d111804, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d92479 q = 1) (hb : d111805 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d92479, d111805, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d92479, d111805, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro17545 (p : Pattern) (ha : d92483 p = 1) (hb : d111744 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d92397 q = 1) (hb : d98846 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d92397, d98846, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17529 q ha hb
    | true =>
      simp only [d92397, d98846, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d92398 q = 1) (hb : d98847 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d92398, d98847, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92398, d98847, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d482 q = 1) (hb : d52229 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d482, d52229, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro61 q ha hb
    | true =>
      simp only [d482, d52229, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d483 q = 1) (hb : d52230 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d483, d52230, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d483, d52230, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d92480 q = 1) (hb : d111741 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d92480, d111741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d92480, d111741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d92481 q = 1) (hb : d111742 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d92481, d111742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d92481, d111742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d92482 q = 1) (hb : d111743 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d92482, d111743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d92482, d111743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d92483 q = 1) (hb : d111744 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d92483, d111744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92483, d111744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro17546 (p : Pattern) (ha : d92489 p = 1) (hb : d111811 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d92484 q = 1) (hb : d111806 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d92484, d111806, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17545 q ha hb
    | true =>
      simp only [d92484, d111806, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro63 q hb ha
  have h2 (q : Pattern) (ha : d92485 q = 1) (hb : d111807 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d92485, d111807, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92485, d111807, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d92486 q = 1) (hb : d111808 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d92486, d111808, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d92486, d111808, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d92487 q = 1) (hb : d111809 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d92487, d111809, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92487, d111809, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d92488 q = 1) (hb : d111810 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d92488, d111810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92488, d111810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d92489 q = 1) (hb : d111811 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d92489, d111811, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92489, d111811, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro17547 (p : Pattern) (ha : d92492 p = 1) (hb : d111761 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d92397 q = 1) (hb : d98846 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d92397, d98846, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17529 q ha hb
    | true =>
      simp only [d92397, d98846, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d92398 q = 1) (hb : d98847 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d92398, d98847, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92398, d98847, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d482 q = 1) (hb : d52229 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d482, d52229, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro61 q ha hb
    | true =>
      simp only [d482, d52229, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d483 q = 1) (hb : d52230 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d483, d52230, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d483, d52230, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d92480 q = 1) (hb : d111741 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d92480, d111741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d92480, d111741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d92481 q = 1) (hb : d111742 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d92481, d111742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d92481, d111742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d92482 q = 1) (hb : d111743 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d92482, d111743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d92482, d111743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d92492 q = 1) (hb : d111761 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d92492, d111761, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d92492, d111761, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro17548 (p : Pattern) (ha : d92498 p = 1) (hb : d111819 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d92484 q = 1) (hb : d111806 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d92484, d111806, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17545 q ha hb
    | true =>
      simp only [d92484, d111806, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro63 q hb ha
  have h2 (q : Pattern) (ha : d92485 q = 1) (hb : d111807 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d92485, d111807, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92485, d111807, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d92486 q = 1) (hb : d111808 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d92486, d111808, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d92486, d111808, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d92487 q = 1) (hb : d111809 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d92487, d111809, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92487, d111809, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d92488 q = 1) (hb : d111810 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d92488, d111810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92488, d111810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d92493 q = 1) (hb : d111814 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d92493, d111814, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17547 q ha hb
    | true =>
      simp only [d92493, d111814, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro66 q hb ha
  have h7 (q : Pattern) (ha : d92494 q = 1) (hb : d111815 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d92494, d111815, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92494, d111815, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d92495 q = 1) (hb : d111816 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d92495, d111816, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d92495, d111816, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d92496 q = 1) (hb : d111817 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d92496, d111817, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92496, d111817, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d92497 q = 1) (hb : d111818 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d92497, d111818, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92497, d111818, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d92498 q = 1) (hb : d111819 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d92498, d111819, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d92498, d111819, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro17549 (p : Pattern) (ha : d92503 p = 1) (hb : d111824 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d92397 q = 1) (hb : d98846 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d92397, d98846, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17529 q ha hb
    | true =>
      simp only [d92397, d98846, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d92398 q = 1) (hb : d98847 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d92398, d98847, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92398, d98847, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d482 q = 1) (hb : d52229 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d482, d52229, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro61 q ha hb
    | true =>
      simp only [d482, d52229, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d483 q = 1) (hb : d52230 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d483, d52230, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d483, d52230, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d92480 q = 1) (hb : d111741 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d92480, d111741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d92480, d111741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d92481 q = 1) (hb : d111742 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d92481, d111742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d92481, d111742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d92502 q = 1) (hb : d111823 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d92502, d111823, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92502, d111823, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d92503 q = 1) (hb : d111824 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d92503, d111824, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92503, d111824, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro17550 (p : Pattern) (ha : d92510 p = 1) (hb : d111831 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d92397 q = 1) (hb : d98846 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d92397, d98846, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17529 q ha hb
    | true =>
      simp only [d92397, d98846, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d92398 q = 1) (hb : d98847 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d92398, d98847, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92398, d98847, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d482 q = 1) (hb : d52229 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d482, d52229, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro61 q ha hb
    | true =>
      simp only [d482, d52229, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d483 q = 1) (hb : d52230 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d483, d52230, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d483, d52230, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d92480 q = 1) (hb : d111741 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d92480, d111741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d92480, d111741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d92508 q = 1) (hb : d111829 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d92508, d111829, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92508, d111829, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d92509 q = 1) (hb : d111830 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d92509, d111830, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d92509, d111830, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d92510 q = 1) (hb : d111831 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d92510, d111831, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92510, d111831, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro17551 (p : Pattern) (ha : d81587 p = 1) (hb : d98845 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d325 q = 1) (hb : d52124 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d325, d52124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43 q ha hb
    | true =>
      simp only [d325, d52124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20 q ha hb
  have h2 (q : Pattern) (ha : d326 q = 1) (hb : d52125 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d326, d52125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d326, d52125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d327 q = 1) (hb : d52126 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d327, d52126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d327, d52126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d6797 q = 1) (hb : d81585 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d6797, d81585, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d6797, d81585, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d68918 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d81586 q = 1) (hb : d98844 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d81586, d98844, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d81586, d98844, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d81587 q = 1) (hb : d98845 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d81587, d98845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d81587, d98845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h7 p ha hb
theorem andIntro17552 (p : Pattern) (ha : d92516 p = 1) (hb : d111836 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d549 q = 1) (hb : d52296 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d549, d52296, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro77 q ha hb
    | true =>
      simp only [d549, d52296, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43 q ha hb
  have h2 (q : Pattern) (ha : d550 q = 1) (hb : d52297 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d550, d52297, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d550, d52297, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d551 q = 1) (hb : d52298 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d551, d52298, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d551, d52298, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d8451 q = 1) (hb : d92514 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d8451, d92514, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d8451, d92514, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d81585 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d92515 q = 1) (hb : d111835 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d92515, d111835, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d92515, d111835, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d92516 q = 1) (hb : d111836 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d92516, d111836, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d92516, d111836, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h7 p ha hb
theorem andIntro17553 (p : Pattern) (ha : d92522 p = 1) (hb : d111842 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d92517 q = 1) (hb : d111837 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d92517, d111837, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17552 q ha hb
    | true =>
      simp only [d92517, d111837, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d92518 q = 1) (hb : d111838 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d92518, d111838, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92518, d111838, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d81588 q = 1) (hb : d98846 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d81588, d98846, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17551 q ha hb
    | true =>
      simp only [d81588, d98846, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d81589 q = 1) (hb : d98847 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d81589, d98847, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d81589, d98847, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d92519 q = 1) (hb : d111839 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d92519, d111839, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d92519, d111839, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d92520 q = 1) (hb : d111840 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d92520, d111840, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d92520, d111840, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d92521 q = 1) (hb : d111841 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d92521, d111841, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d92521, d111841, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d92522 q = 1) (hb : d111842 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d92522, d111842, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92522, d111842, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro17554 (p : Pattern) (ha : d92526 p = 1) (hb : d111744 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d81588 q = 1) (hb : d98846 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d81588, d98846, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17551 q ha hb
    | true =>
      simp only [d81588, d98846, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d81589 q = 1) (hb : d98847 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d81589, d98847, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d81589, d98847, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d482 q = 1) (hb : d52229 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d482, d52229, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro61 q ha hb
    | true =>
      simp only [d482, d52229, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d483 q = 1) (hb : d52230 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d483, d52230, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d483, d52230, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d92523 q = 1) (hb : d111741 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d92523, d111741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d92523, d111741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d92524 q = 1) (hb : d111742 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d92524, d111742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d92524, d111742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d92525 q = 1) (hb : d111743 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d92525, d111743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d92525, d111743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d92526 q = 1) (hb : d111744 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d92526, d111744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92526, d111744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro17555 (p : Pattern) (ha : d92532 p = 1) (hb : d111848 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d92397 q = 1) (hb : d98846 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d92397, d98846, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17529 q ha hb
    | true =>
      simp only [d92397, d98846, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d92398 q = 1) (hb : d98847 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d92398, d98847, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92398, d98847, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d92529 q = 1) (hb : d111845 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d92529, d111845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d92529, d111845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d92530 q = 1) (hb : d111846 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d92530, d111846, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d92530, d111846, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d92531 q = 1) (hb : d111847 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d92531, d111847, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d92531, d111847, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d92532 q = 1) (hb : d111848 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d92532, d111848, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92532, d111848, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro17556 (p : Pattern) (ha : d92538 p = 1) (hb : d111854 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d92504 q = 1) (hb : d111825 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d92504, d111825, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17549 q ha hb
    | true =>
      simp only [d92504, d111825, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro88 q hb ha
  have h2 (q : Pattern) (ha : d92505 q = 1) (hb : d111826 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d92505, d111826, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92505, d111826, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d92506 q = 1) (hb : d111827 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d92506, d111827, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d92506, d111827, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d92507 q = 1) (hb : d111828 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d92507, d111828, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92507, d111828, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d92511 q = 1) (hb : d111832 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d92511, d111832, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17550 q ha hb
    | true =>
      simp only [d92511, d111832, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro90 q hb ha
  have h6 (q : Pattern) (ha : d92512 q = 1) (hb : d111833 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d92512, d111833, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92512, d111833, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d92513 q = 1) (hb : d111834 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d92513, d111834, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d92513, d111834, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d92527 q = 1) (hb : d111843 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d92527, d111843, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17553 q ha hb
    | true =>
      simp only [d92527, d111843, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17554 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d92484 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d92528 q = 1) (hb : d111844 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d92528, d111844, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d92528, d111844, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
  have h11 (q : Pattern) (ha : d92533 q = 1) (hb : d111849 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d92533, d111849, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17555 q ha hb
    | true =>
      simp only [d92533, d111849, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d92534 q = 1) (hb : d111850 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d92534, d111850, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d92534, d111850, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d92535 q = 1) (hb : d111851 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d92535, d111851, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d92535, d111851, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d92536 q = 1) (hb : d111852 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d92536, d111852, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d92536, d111852, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d92537 q = 1) (hb : d111853 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d92537, d111853, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d92537, d111853, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d92538 q = 1) (hb : d111854 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d92538, d111854, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92538, d111854, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  exact h16 p ha hb
theorem andIntro17557 (p : Pattern) (ha : d92539 p = 1) (hb : d111855 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d92397 q = 1) (hb : d98846 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d92397, d98846, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17529 q ha hb
    | true =>
      simp only [d92397, d98846, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d92398 q = 1) (hb : d98847 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d92398, d98847, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92398, d98847, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d482 q = 1) (hb : d52229 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d482, d52229, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro61 q ha hb
    | true =>
      simp only [d482, d52229, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d483 q = 1) (hb : d52230 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d483, d52230, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d483, d52230, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d92480 q = 1) (hb : d111741 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d92480, d111741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d92480, d111741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d92481 q = 1) (hb : d111742 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d92481, d111742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d92481, d111742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d92502 q = 1) (hb : d111823 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d92502, d111823, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92502, d111823, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d92539 q = 1) (hb : d111855 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d92539, d111855, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d92539, d111855, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro17558 (p : Pattern) (ha : d92544 p = 1) (hb : d111860 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d92397 q = 1) (hb : d98846 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d92397, d98846, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17529 q ha hb
    | true =>
      simp only [d92397, d98846, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d92398 q = 1) (hb : d98847 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d92398, d98847, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92398, d98847, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d482 q = 1) (hb : d52229 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d482, d52229, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro61 q ha hb
    | true =>
      simp only [d482, d52229, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d483 q = 1) (hb : d52230 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d483, d52230, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d483, d52230, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d92480 q = 1) (hb : d111741 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d92480, d111741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d92480, d111741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d92508 q = 1) (hb : d111829 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d92508, d111829, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92508, d111829, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d92509 q = 1) (hb : d111830 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d92509, d111830, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d92509, d111830, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d92544 q = 1) (hb : d111860 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d92544, d111860, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d92544, d111860, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro17559 (p : Pattern) (ha : d92548 p = 1) (hb : d111864 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d92517 q = 1) (hb : d111837 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d92517, d111837, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17552 q ha hb
    | true =>
      simp only [d92517, d111837, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d92518 q = 1) (hb : d111838 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d92518, d111838, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92518, d111838, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d81588 q = 1) (hb : d98846 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d81588, d98846, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17551 q ha hb
    | true =>
      simp only [d81588, d98846, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d81589 q = 1) (hb : d98847 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d81589, d98847, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d81589, d98847, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d92519 q = 1) (hb : d111839 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d92519, d111839, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d92519, d111839, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d92520 q = 1) (hb : d111840 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d92520, d111840, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d92520, d111840, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d92521 q = 1) (hb : d111841 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d92521, d111841, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d92521, d111841, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d92548 q = 1) (hb : d111864 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d92548, d111864, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d92548, d111864, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro17560 (p : Pattern) (ha : d92549 p = 1) (hb : d111761 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d81588 q = 1) (hb : d98846 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d81588, d98846, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17551 q ha hb
    | true =>
      simp only [d81588, d98846, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d81589 q = 1) (hb : d98847 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d81589, d98847, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d81589, d98847, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d482 q = 1) (hb : d52229 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d482, d52229, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro61 q ha hb
    | true =>
      simp only [d482, d52229, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d483 q = 1) (hb : d52230 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d483, d52230, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d483, d52230, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d92523 q = 1) (hb : d111741 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d92523, d111741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d92523, d111741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d92524 q = 1) (hb : d111742 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d92524, d111742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d92524, d111742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d92525 q = 1) (hb : d111743 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d92525, d111743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d92525, d111743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d92549 q = 1) (hb : d111761 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d92549, d111761, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d92549, d111761, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro17561 (p : Pattern) (ha : d92552 p = 1) (hb : d111867 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d92397 q = 1) (hb : d98846 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d92397, d98846, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17529 q ha hb
    | true =>
      simp only [d92397, d98846, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d92398 q = 1) (hb : d98847 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d92398, d98847, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92398, d98847, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d92529 q = 1) (hb : d111845 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d92529, d111845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d92529, d111845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d92530 q = 1) (hb : d111846 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d92530, d111846, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d92530, d111846, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d92531 q = 1) (hb : d111847 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d92531, d111847, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d92531, d111847, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d92552 q = 1) (hb : d111867 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d92552, d111867, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d92552, d111867, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro17562 (p : Pattern) (ha : d92558 p = 1) (hb : d111873 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d92504 q = 1) (hb : d111825 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d92504, d111825, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17549 q ha hb
    | true =>
      simp only [d92504, d111825, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro88 q hb ha
  have h2 (q : Pattern) (ha : d92505 q = 1) (hb : d111826 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d92505, d111826, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92505, d111826, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d92506 q = 1) (hb : d111827 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d92506, d111827, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d92506, d111827, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d92507 q = 1) (hb : d111828 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d92507, d111828, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92507, d111828, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d92511 q = 1) (hb : d111832 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d92511, d111832, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17550 q ha hb
    | true =>
      simp only [d92511, d111832, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro90 q hb ha
  have h6 (q : Pattern) (ha : d92512 q = 1) (hb : d111833 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d92512, d111833, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92512, d111833, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d92513 q = 1) (hb : d111834 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d92513, d111834, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d92513, d111834, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d92527 q = 1) (hb : d111843 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d92527, d111843, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17553 q ha hb
    | true =>
      simp only [d92527, d111843, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17554 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d92484 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d92528 q = 1) (hb : d111844 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d92528, d111844, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d92528, d111844, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
  have h11 (q : Pattern) (ha : d92533 q = 1) (hb : d111849 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d92533, d111849, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17555 q ha hb
    | true =>
      simp only [d92533, d111849, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d92534 q = 1) (hb : d111850 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d92534, d111850, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d92534, d111850, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d92535 q = 1) (hb : d111851 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d92535, d111851, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d92535, d111851, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d92536 q = 1) (hb : d111852 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d92536, d111852, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d92536, d111852, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d92537 q = 1) (hb : d111853 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d92537, d111853, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d92537, d111853, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d92540 q = 1) (hb : d111856 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d92540, d111856, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17557 q ha hb
    | true =>
      simp only [d92540, d111856, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro94 q hb ha
  have h17 (q : Pattern) (ha : d92541 q = 1) (hb : d111857 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d92541, d111857, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92541, d111857, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d92542 q = 1) (hb : d111858 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d92542, d111858, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d92542, d111858, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h19 (q : Pattern) (ha : d92543 q = 1) (hb : d111859 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d92543, d111859, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92543, d111859, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d92545 q = 1) (hb : d111861 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d92545, d111861, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17558 q ha hb
    | true =>
      simp only [d92545, d111861, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96 q hb ha
  have h21 (q : Pattern) (ha : d92546 q = 1) (hb : d111862 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d92546, d111862, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92546, d111862, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
  have h22 (q : Pattern) (ha : d92547 q = 1) (hb : d111863 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d92547, d111863, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d92547, d111863, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h23 (q : Pattern) (ha : d92550 q = 1) (hb : d111865 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d92550, d111865, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17559 q ha hb
    | true =>
      simp only [d92550, d111865, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17560 q ha hb
  have h24 (q : Pattern) (ha : d0 q = 1) (hb : d92493 q = 1) : d0 q = 1 := by
    exact ha
  have h25 (q : Pattern) (ha : d92551 q = 1) (hb : d111866 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d92551, d111866, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
    | true =>
      simp only [d92551, d111866, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q hb ha
  have h26 (q : Pattern) (ha : d92553 q = 1) (hb : d111868 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d92553, d111868, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17561 q ha hb
    | true =>
      simp only [d92553, d111868, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h27 (q : Pattern) (ha : d92554 q = 1) (hb : d111869 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d92554, d111869, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h26 q ha hb
    | true =>
      simp only [d92554, d111869, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h28 (q : Pattern) (ha : d92555 q = 1) (hb : d111870 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d92555, d111870, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q ha hb
    | true =>
      simp only [d92555, d111870, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h27 q ha hb
  have h29 (q : Pattern) (ha : d92556 q = 1) (hb : d111871 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d92556, d111871, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
    | true =>
      simp only [d92556, d111871, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h28 q ha hb
  have h30 (q : Pattern) (ha : d92557 q = 1) (hb : d111872 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d92557, d111872, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d92557, d111872, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h29 q ha hb
  have h31 (q : Pattern) (ha : d92558 q = 1) (hb : d111873 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d92558, d111873, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d92558, d111873, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h30 q ha hb
  exact h31 p ha hb
theorem andIntro17563 (p : Pattern) (ha : d92565 p = 1) (hb : d111875 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d92560 q = 1) (hb : d111806 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d92560, d111806, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17554 q ha hb
    | true =>
      simp only [d92560, d111806, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro63 q hb ha
  have h2 (q : Pattern) (ha : d92561 q = 1) (hb : d111807 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d92561, d111807, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92561, d111807, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d92562 q = 1) (hb : d111808 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d92562, d111808, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d92562, d111808, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d92563 q = 1) (hb : d111809 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d92563, d111809, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92563, d111809, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d92564 q = 1) (hb : d111810 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d92564, d111810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92564, d111810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d633 q = 1) (hb : d52337 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d633, d52337, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro63 q ha hb
    | true =>
      simp only [d633, d52337, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d634 q = 1) (hb : d52338 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d634, d52338, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d634, d52338, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d635 q = 1) (hb : d52339 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d635, d52339, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d635, d52339, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d636 q = 1) (hb : d52340 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d636, d52340, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d636, d52340, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d637 q = 1) (hb : d52341 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d637, d52341, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d637, d52341, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d92565 q = 1) (hb : d111875 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d92565, d111875, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d92565, d111875, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
  exact h11 p ha hb
theorem andIntro17564 (p : Pattern) (ha : d92572 p = 1) (hb : d111882 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d92550 q = 1) (hb : d111865 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d92550, d111865, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17559 q ha hb
    | true =>
      simp only [d92550, d111865, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17560 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d92493 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d92551 q = 1) (hb : d111866 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d92551, d111866, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d92551, d111866, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d92553 q = 1) (hb : d111868 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d92553, d111868, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17561 q ha hb
    | true =>
      simp only [d92553, d111868, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d92554 q = 1) (hb : d111869 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d92554, d111869, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d92554, d111869, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d92555 q = 1) (hb : d111870 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d92555, d111870, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d92555, d111870, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d92570 q = 1) (hb : d111880 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d92570, d111880, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92570, d111880, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d92571 q = 1) (hb : d111881 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d92571, d111881, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92571, d111881, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d92572 q = 1) (hb : d111882 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d92572, d111882, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92572, d111882, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro17565 (p : Pattern) (ha : d81633 p = 1) (hb : d98878 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d418 q = 1) (hb : d52184 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d418, d52184, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47 q ha hb
    | true =>
      simp only [d418, d52184, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24 q ha hb
  have h2 (q : Pattern) (ha : d419 q = 1) (hb : d52185 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d419, d52185, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d419, d52185, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d420 q = 1) (hb : d52186 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d420, d52186, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d420, d52186, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d6843 q = 1) (hb : d81631 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d6843, d81631, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d6843, d81631, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d75844 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d81632 q = 1) (hb : d98877 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d81632, d98877, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d81632, d98877, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d81633 q = 1) (hb : d98878 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d81633, d98878, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d81633, d98878, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h7 p ha hb
theorem andIntro17566 (p : Pattern) (ha : d92580 p = 1) (hb : d111889 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d665 q = 1) (hb : d52369 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d665, d52369, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro81 q ha hb
    | true =>
      simp only [d665, d52369, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47 q ha hb
  have h2 (q : Pattern) (ha : d666 q = 1) (hb : d52370 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d666, d52370, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d666, d52370, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d667 q = 1) (hb : d52371 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d667, d52371, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d667, d52371, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d8527 q = 1) (hb : d92578 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d8527, d92578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d8527, d92578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d81631 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d92579 q = 1) (hb : d111888 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d92579, d111888, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d92579, d111888, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d92580 q = 1) (hb : d111889 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d92580, d111889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d92580, d111889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h7 p ha hb
theorem andIntro17567 (p : Pattern) (ha : d92586 p = 1) (hb : d111895 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d92581 q = 1) (hb : d111890 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d92581, d111890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17566 q ha hb
    | true =>
      simp only [d92581, d111890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d92582 q = 1) (hb : d111891 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d92582, d111891, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92582, d111891, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d81634 q = 1) (hb : d98879 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d81634, d98879, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17565 q ha hb
    | true =>
      simp only [d81634, d98879, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d81635 q = 1) (hb : d98880 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d81635, d98880, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d81635, d98880, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d92583 q = 1) (hb : d111892 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d92583, d111892, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d92583, d111892, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d92584 q = 1) (hb : d111893 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d92584, d111893, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d92584, d111893, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d92585 q = 1) (hb : d111894 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d92585, d111894, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d92585, d111894, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d92586 q = 1) (hb : d111895 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d92586, d111895, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d92586, d111895, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro17568 (p : Pattern) (ha : d92590 p = 1) (hb : d111786 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d81634 q = 1) (hb : d98879 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d81634, d98879, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17565 q ha hb
    | true =>
      simp only [d81634, d98879, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d81635 q = 1) (hb : d98880 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d81635, d98880, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d81635, d98880, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d684 q = 1) (hb : d52388 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d684, d52388, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro71 q ha hb
    | true =>
      simp only [d684, d52388, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d685 q = 1) (hb : d52389 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d685, d52389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d685, d52389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d92587 q = 1) (hb : d111783 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d92587, d111783, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d92587, d111783, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d92588 q = 1) (hb : d111784 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d92588, d111784, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d92588, d111784, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d92589 q = 1) (hb : d111785 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d92589, d111785, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d92589, d111785, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d92590 q = 1) (hb : d111786 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d92590, d111786, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d92590, d111786, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro17569 (p : Pattern) (ha : d92601 p = 1) (hb : d111901 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d92450 q = 1) (hb : d98879 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d92450, d98879, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17540 q ha hb
    | true =>
      simp only [d92450, d98879, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d92451 q = 1) (hb : d98880 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d92451, d98880, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92451, d98880, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d92598 q = 1) (hb : d111898 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d92598, d111898, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d92598, d111898, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d92599 q = 1) (hb : d111899 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d92599, d111899, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d92599, d111899, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d92600 q = 1) (hb : d111900 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d92600, d111900, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d92600, d111900, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d92601 q = 1) (hb : d111901 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d92601, d111901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d92601, d111901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro17570 (p : Pattern) (ha : d92607 p = 1) (hb : d111907 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d92591 q = 1) (hb : d111896 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d92591, d111896, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17567 q ha hb
    | true =>
      simp only [d92591, d111896, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17568 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d92596 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d92597 q = 1) (hb : d111897 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d92597, d111897, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d92597, d111897, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d92602 q = 1) (hb : d111902 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d92602, d111902, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17569 q ha hb
    | true =>
      simp only [d92602, d111902, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d92603 q = 1) (hb : d111903 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d92603, d111903, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d92603, d111903, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d92604 q = 1) (hb : d111904 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d92604, d111904, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d92604, d111904, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d92605 q = 1) (hb : d111905 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d92605, d111905, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92605, d111905, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d92606 q = 1) (hb : d111906 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d92606, d111906, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92606, d111906, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d92607 q = 1) (hb : d111907 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d92607, d111907, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92607, d111907, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro17571 (p : Pattern) (ha : d92613 p = 1) (hb : d111913 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d92490 q = 1) (hb : d111812 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d92490, d111812, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92490, d111812, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17546 q ha hb
  have h2 (q : Pattern) (ha : d92491 q = 1) (hb : d111813 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d92491, d111813, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d92491, d111813, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d92499 q = 1) (hb : d111820 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d92499, d111820, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17546 q ha hb
    | true =>
      simp only [d92499, d111820, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17548 q ha hb
  have h4 (q : Pattern) (ha : d92500 q = 1) (hb : d111821 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d92500, d111821, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d92500, d111821, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d92501 q = 1) (hb : d111822 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d92501, d111822, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d92501, d111822, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d92559 q = 1) (hb : d111874 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d92559, d111874, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17556 q ha hb
    | true =>
      simp only [d92559, d111874, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17562 q ha hb
  have h7 (q : Pattern) (ha : d92566 q = 1) (hb : d111876 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d92566, d111876, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17563 q ha hb
    | true =>
      simp only [d92566, d111876, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro69 q hb ha
  have h8 (q : Pattern) (ha : d92567 q = 1) (hb : d111877 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d92567, d111877, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d92567, d111877, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d92568 q = 1) (hb : d111878 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d92568, d111878, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d92568, d111878, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h10 (q : Pattern) (ha : d92569 q = 1) (hb : d111879 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d92569, d111879, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d92569, d111879, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d92573 q = 1) (hb : d111883 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d92573, d111883, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92573, d111883, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17564 q ha hb
  have h12 (q : Pattern) (ha : d654 q = 1) (hb : d52358 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d654, d52358, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d654, d52358, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro70 q ha hb
  have h13 (q : Pattern) (ha : d92574 q = 1) (hb : d111884 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d92574, d111884, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d92574, d111884, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
  have h14 (q : Pattern) (ha : d92575 q = 1) (hb : d111885 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d92575, d111885, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d92575, d111885, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h15 (q : Pattern) (ha : d92576 q = 1) (hb : d111886 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d92576, d111886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d92576, d111886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h16 (q : Pattern) (ha : d92577 q = 1) (hb : d111887 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d92577, d111887, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d92577, d111887, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d92608 q = 1) (hb : d111908 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d92608, d111908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92608, d111908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17570 q ha hb
  have h18 (q : Pattern) (ha : d737 q = 1) (hb : d52414 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d737, d52414, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d737, d52414, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73 q ha hb
  have h19 (q : Pattern) (ha : d92609 q = 1) (hb : d111909 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d92609, d111909, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d92609, d111909, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q hb ha
  have h20 (q : Pattern) (ha : d92610 q = 1) (hb : d111910 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d92610, d111910, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d92610, d111910, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h21 (q : Pattern) (ha : d92611 q = 1) (hb : d111911 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d92611, d111911, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d92611, d111911, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h22 (q : Pattern) (ha : d92612 q = 1) (hb : d111912 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d92612, d111912, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d92612, d111912, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h23 (q : Pattern) (ha : d92613 q = 1) (hb : d111913 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d92613, d111913, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d92613, d111913, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
  exact h23 p ha hb
theorem andIntro17572 (p : Pattern) (ha : d92619 p = 1) (hb : d111919 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d92614 q = 1) (hb : d111914 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d92614, d111914, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92614, d111914, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17571 q ha hb
  have h2 (q : Pattern) (ha : d92615 q = 1) (hb : d111915 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d92615, d111915, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92615, d111915, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d92616 q = 1) (hb : d111916 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d92616, d111916, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92616, d111916, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d92617 q = 1) (hb : d111917 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d92617, d111917, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92617, d111917, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d92618 q = 1) (hb : d111918 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d92618, d111918, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92618, d111918, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d92619 q = 1) (hb : d111919 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d92619, d111919, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92619, d111919, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro17573 (p : Pattern) (ha : d92622 p = 1) (hb : d98905 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d759 q = 1) (hb : d52436 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d759, d52436, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro101 q ha hb
    | true =>
      simp only [d759, d52436, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro102 q ha hb
  have h2 (q : Pattern) (ha : d760 q = 1) (hb : d52437 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d760, d52437, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d760, d52437, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d761 q = 1) (hb : d52438 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d761, d52438, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d761, d52438, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d6875 q = 1) (hb : d81663 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d6875, d81663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d6875, d81663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d52444 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d92621 q = 1) (hb : d98904 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d92621, d98904, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d92621, d98904, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d92622 q = 1) (hb : d98905 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d92622, d98905, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d92622, d98905, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h7 p ha hb
theorem andIntro17574 (p : Pattern) (ha : d92628 p = 1) (hb : d111924 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d92623 q = 1) (hb : d98906 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d92623, d98906, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17573 q ha hb
    | true =>
      simp only [d92623, d98906, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d92624 q = 1) (hb : d98907 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d92624, d98907, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92624, d98907, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d774 q = 1) (hb : d52451 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d774, d52451, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105 q ha hb
    | true =>
      simp only [d774, d52451, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d775 q = 1) (hb : d52452 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d775, d52452, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d775, d52452, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d92625 q = 1) (hb : d111921 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d92625, d111921, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d92625, d111921, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d92626 q = 1) (hb : d111922 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d92626, d111922, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d92626, d111922, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d92627 q = 1) (hb : d111923 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d92627, d111923, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d92627, d111923, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d92628 q = 1) (hb : d111924 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d92628, d111924, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92628, d111924, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro17575 (p : Pattern) (ha : d92634 p = 1) (hb : d111930 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d92629 q = 1) (hb : d111925 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d92629, d111925, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17574 q ha hb
    | true =>
      simp only [d92629, d111925, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro107 q hb ha
  have h2 (q : Pattern) (ha : d92630 q = 1) (hb : d111926 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d92630, d111926, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92630, d111926, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d92631 q = 1) (hb : d111927 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d92631, d111927, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d92631, d111927, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d92632 q = 1) (hb : d111928 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d92632, d111928, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92632, d111928, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d92633 q = 1) (hb : d111929 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d92633, d111929, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92633, d111929, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d92634 q = 1) (hb : d111930 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d92634, d111930, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92634, d111930, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro17576 (p : Pattern) (ha : d92637 p = 1) (hb : d111933 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d92623 q = 1) (hb : d98906 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d92623, d98906, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17573 q ha hb
    | true =>
      simp only [d92623, d98906, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d92624 q = 1) (hb : d98907 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d92624, d98907, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92624, d98907, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d774 q = 1) (hb : d52451 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d774, d52451, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105 q ha hb
    | true =>
      simp only [d774, d52451, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d775 q = 1) (hb : d52452 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d775, d52452, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d775, d52452, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d92625 q = 1) (hb : d111921 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d92625, d111921, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d92625, d111921, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d92626 q = 1) (hb : d111922 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d92626, d111922, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d92626, d111922, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d92627 q = 1) (hb : d111923 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d92627, d111923, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d92627, d111923, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d92637 q = 1) (hb : d111933 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d92637, d111933, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d92637, d111933, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro17577 (p : Pattern) (ha : d92643 p = 1) (hb : d111939 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d92629 q = 1) (hb : d111925 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d92629, d111925, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17574 q ha hb
    | true =>
      simp only [d92629, d111925, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro107 q hb ha
  have h2 (q : Pattern) (ha : d92630 q = 1) (hb : d111926 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d92630, d111926, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92630, d111926, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d92631 q = 1) (hb : d111927 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d92631, d111927, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d92631, d111927, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d92632 q = 1) (hb : d111928 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d92632, d111928, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92632, d111928, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d92633 q = 1) (hb : d111929 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d92633, d111929, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92633, d111929, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d92638 q = 1) (hb : d111934 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d92638, d111934, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17576 q ha hb
    | true =>
      simp only [d92638, d111934, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro110 q hb ha
  have h7 (q : Pattern) (ha : d92639 q = 1) (hb : d111935 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d92639, d111935, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92639, d111935, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d92640 q = 1) (hb : d111936 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d92640, d111936, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d92640, d111936, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d92641 q = 1) (hb : d111937 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d92641, d111937, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92641, d111937, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d92642 q = 1) (hb : d111938 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d92642, d111938, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92642, d111938, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d92643 q = 1) (hb : d111939 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d92643, d111939, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d92643, d111939, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro17578 (p : Pattern) (ha : d92648 p = 1) (hb : d111944 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d92623 q = 1) (hb : d98906 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d92623, d98906, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17573 q ha hb
    | true =>
      simp only [d92623, d98906, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d92624 q = 1) (hb : d98907 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d92624, d98907, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92624, d98907, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d774 q = 1) (hb : d52451 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d774, d52451, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105 q ha hb
    | true =>
      simp only [d774, d52451, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d775 q = 1) (hb : d52452 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d775, d52452, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d775, d52452, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d92625 q = 1) (hb : d111921 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d92625, d111921, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d92625, d111921, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d92626 q = 1) (hb : d111922 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d92626, d111922, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d92626, d111922, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d92647 q = 1) (hb : d111943 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d92647, d111943, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92647, d111943, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d92648 q = 1) (hb : d111944 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d92648, d111944, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92648, d111944, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro17579 (p : Pattern) (ha : d92655 p = 1) (hb : d111951 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d92623 q = 1) (hb : d98906 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d92623, d98906, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17573 q ha hb
    | true =>
      simp only [d92623, d98906, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d92624 q = 1) (hb : d98907 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d92624, d98907, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92624, d98907, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d774 q = 1) (hb : d52451 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d774, d52451, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105 q ha hb
    | true =>
      simp only [d774, d52451, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d775 q = 1) (hb : d52452 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d775, d52452, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d775, d52452, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d92625 q = 1) (hb : d111921 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d92625, d111921, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d92625, d111921, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d92653 q = 1) (hb : d111949 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d92653, d111949, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92653, d111949, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d92654 q = 1) (hb : d111950 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d92654, d111950, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d92654, d111950, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d92655 q = 1) (hb : d111951 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d92655, d111951, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92655, d111951, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro17580 (p : Pattern) (ha : d81665 p = 1) (hb : d98905 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d759 q = 1) (hb : d52436 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d759, d52436, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro101 q ha hb
    | true =>
      simp only [d759, d52436, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro102 q ha hb
  have h2 (q : Pattern) (ha : d760 q = 1) (hb : d52437 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d760, d52437, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d760, d52437, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d761 q = 1) (hb : d52438 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d761, d52438, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d761, d52438, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d6875 q = 1) (hb : d81663 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d6875, d81663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d6875, d81663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d69010 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d81664 q = 1) (hb : d98904 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d81664, d98904, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d81664, d98904, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d81665 q = 1) (hb : d98905 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d81665, d98905, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d81665, d98905, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h7 p ha hb
theorem andIntro17581 (p : Pattern) (ha : d92661 p = 1) (hb : d111956 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d840 q = 1) (hb : d52517 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d840, d52517, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro123 q ha hb
    | true =>
      simp only [d840, d52517, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro101 q ha hb
  have h2 (q : Pattern) (ha : d841 q = 1) (hb : d52518 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d841, d52518, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d841, d52518, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d842 q = 1) (hb : d52519 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d842, d52519, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d842, d52519, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d8613 q = 1) (hb : d92659 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d8613, d92659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d8613, d92659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d81663 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d92660 q = 1) (hb : d111955 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d92660, d111955, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d92660, d111955, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d92661 q = 1) (hb : d111956 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d92661, d111956, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d92661, d111956, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h7 p ha hb
theorem andIntro17582 (p : Pattern) (ha : d92667 p = 1) (hb : d111962 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d92662 q = 1) (hb : d111957 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d92662, d111957, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17581 q ha hb
    | true =>
      simp only [d92662, d111957, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d92663 q = 1) (hb : d111958 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d92663, d111958, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92663, d111958, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d81666 q = 1) (hb : d98906 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d81666, d98906, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17580 q ha hb
    | true =>
      simp only [d81666, d98906, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d81667 q = 1) (hb : d98907 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d81667, d98907, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d81667, d98907, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d92664 q = 1) (hb : d111959 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d92664, d111959, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d92664, d111959, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d92665 q = 1) (hb : d111960 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d92665, d111960, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d92665, d111960, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d92666 q = 1) (hb : d111961 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d92666, d111961, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d92666, d111961, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d92667 q = 1) (hb : d111962 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d92667, d111962, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92667, d111962, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro17583 (p : Pattern) (ha : d92671 p = 1) (hb : d111924 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d81666 q = 1) (hb : d98906 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d81666, d98906, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17580 q ha hb
    | true =>
      simp only [d81666, d98906, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d81667 q = 1) (hb : d98907 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d81667, d98907, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d81667, d98907, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d774 q = 1) (hb : d52451 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d774, d52451, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105 q ha hb
    | true =>
      simp only [d774, d52451, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d775 q = 1) (hb : d52452 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d775, d52452, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d775, d52452, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d92668 q = 1) (hb : d111921 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d92668, d111921, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d92668, d111921, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d92669 q = 1) (hb : d111922 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d92669, d111922, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d92669, d111922, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d92670 q = 1) (hb : d111923 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d92670, d111923, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d92670, d111923, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d92671 q = 1) (hb : d111924 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d92671, d111924, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92671, d111924, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro17584 (p : Pattern) (ha : d92677 p = 1) (hb : d111968 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d92623 q = 1) (hb : d98906 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d92623, d98906, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17573 q ha hb
    | true =>
      simp only [d92623, d98906, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d92624 q = 1) (hb : d98907 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d92624, d98907, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92624, d98907, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d92674 q = 1) (hb : d111965 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d92674, d111965, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d92674, d111965, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d92675 q = 1) (hb : d111966 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d92675, d111966, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d92675, d111966, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d92676 q = 1) (hb : d111967 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d92676, d111967, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d92676, d111967, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d92677 q = 1) (hb : d111968 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d92677, d111968, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92677, d111968, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro17585 (p : Pattern) (ha : d92683 p = 1) (hb : d111974 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d92649 q = 1) (hb : d111945 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d92649, d111945, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17578 q ha hb
    | true =>
      simp only [d92649, d111945, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro135 q hb ha
  have h2 (q : Pattern) (ha : d92650 q = 1) (hb : d111946 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d92650, d111946, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92650, d111946, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d92651 q = 1) (hb : d111947 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d92651, d111947, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d92651, d111947, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d92652 q = 1) (hb : d111948 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d92652, d111948, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92652, d111948, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d92656 q = 1) (hb : d111952 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d92656, d111952, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17579 q ha hb
    | true =>
      simp only [d92656, d111952, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro137 q hb ha
  have h6 (q : Pattern) (ha : d92657 q = 1) (hb : d111953 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d92657, d111953, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92657, d111953, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d92658 q = 1) (hb : d111954 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d92658, d111954, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d92658, d111954, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d92672 q = 1) (hb : d111963 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d92672, d111963, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17582 q ha hb
    | true =>
      simp only [d92672, d111963, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17583 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d92629 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d92673 q = 1) (hb : d111964 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d92673, d111964, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d92673, d111964, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
  have h11 (q : Pattern) (ha : d92678 q = 1) (hb : d111969 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d92678, d111969, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17584 q ha hb
    | true =>
      simp only [d92678, d111969, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d92679 q = 1) (hb : d111970 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d92679, d111970, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d92679, d111970, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d92680 q = 1) (hb : d111971 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d92680, d111971, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d92680, d111971, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d92681 q = 1) (hb : d111972 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d92681, d111972, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d92681, d111972, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d92682 q = 1) (hb : d111973 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d92682, d111973, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d92682, d111973, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d92683 q = 1) (hb : d111974 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d92683, d111974, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92683, d111974, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  exact h16 p ha hb
theorem andIntro17586 (p : Pattern) (ha : d92684 p = 1) (hb : d111975 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d92623 q = 1) (hb : d98906 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d92623, d98906, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17573 q ha hb
    | true =>
      simp only [d92623, d98906, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d92624 q = 1) (hb : d98907 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d92624, d98907, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92624, d98907, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d774 q = 1) (hb : d52451 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d774, d52451, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105 q ha hb
    | true =>
      simp only [d774, d52451, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d775 q = 1) (hb : d52452 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d775, d52452, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d775, d52452, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d92625 q = 1) (hb : d111921 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d92625, d111921, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d92625, d111921, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d92626 q = 1) (hb : d111922 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d92626, d111922, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d92626, d111922, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d92647 q = 1) (hb : d111943 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d92647, d111943, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92647, d111943, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d92684 q = 1) (hb : d111975 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d92684, d111975, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d92684, d111975, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro17587 (p : Pattern) (ha : d92689 p = 1) (hb : d111980 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d92623 q = 1) (hb : d98906 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d92623, d98906, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17573 q ha hb
    | true =>
      simp only [d92623, d98906, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d92624 q = 1) (hb : d98907 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d92624, d98907, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92624, d98907, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d774 q = 1) (hb : d52451 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d774, d52451, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105 q ha hb
    | true =>
      simp only [d774, d52451, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d775 q = 1) (hb : d52452 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d775, d52452, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d775, d52452, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d92625 q = 1) (hb : d111921 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d92625, d111921, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d92625, d111921, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d92653 q = 1) (hb : d111949 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d92653, d111949, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92653, d111949, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d92654 q = 1) (hb : d111950 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d92654, d111950, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d92654, d111950, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d92689 q = 1) (hb : d111980 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d92689, d111980, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d92689, d111980, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro17588 (p : Pattern) (ha : d92693 p = 1) (hb : d111984 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d92662 q = 1) (hb : d111957 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d92662, d111957, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17581 q ha hb
    | true =>
      simp only [d92662, d111957, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d92663 q = 1) (hb : d111958 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d92663, d111958, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92663, d111958, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d81666 q = 1) (hb : d98906 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d81666, d98906, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17580 q ha hb
    | true =>
      simp only [d81666, d98906, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d81667 q = 1) (hb : d98907 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d81667, d98907, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d81667, d98907, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d92664 q = 1) (hb : d111959 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d92664, d111959, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d92664, d111959, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d92665 q = 1) (hb : d111960 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d92665, d111960, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d92665, d111960, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d92666 q = 1) (hb : d111961 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d92666, d111961, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d92666, d111961, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d92693 q = 1) (hb : d111984 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d92693, d111984, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d92693, d111984, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro17589 (p : Pattern) (ha : d92694 p = 1) (hb : d111933 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d81666 q = 1) (hb : d98906 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d81666, d98906, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17580 q ha hb
    | true =>
      simp only [d81666, d98906, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d81667 q = 1) (hb : d98907 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d81667, d98907, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d81667, d98907, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d774 q = 1) (hb : d52451 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d774, d52451, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105 q ha hb
    | true =>
      simp only [d774, d52451, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d775 q = 1) (hb : d52452 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d775, d52452, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d775, d52452, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d92668 q = 1) (hb : d111921 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d92668, d111921, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d92668, d111921, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d92669 q = 1) (hb : d111922 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d92669, d111922, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d92669, d111922, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d92670 q = 1) (hb : d111923 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d92670, d111923, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d92670, d111923, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d92694 q = 1) (hb : d111933 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d92694, d111933, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d92694, d111933, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro17590 (p : Pattern) (ha : d92697 p = 1) (hb : d111987 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d92623 q = 1) (hb : d98906 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d92623, d98906, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17573 q ha hb
    | true =>
      simp only [d92623, d98906, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d92624 q = 1) (hb : d98907 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d92624, d98907, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92624, d98907, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d92674 q = 1) (hb : d111965 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d92674, d111965, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d92674, d111965, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d92675 q = 1) (hb : d111966 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d92675, d111966, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d92675, d111966, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d92676 q = 1) (hb : d111967 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d92676, d111967, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d92676, d111967, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d92697 q = 1) (hb : d111987 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d92697, d111987, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d92697, d111987, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro17591 (p : Pattern) (ha : d92703 p = 1) (hb : d111993 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d92649 q = 1) (hb : d111945 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d92649, d111945, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17578 q ha hb
    | true =>
      simp only [d92649, d111945, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro135 q hb ha
  have h2 (q : Pattern) (ha : d92650 q = 1) (hb : d111946 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d92650, d111946, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92650, d111946, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d92651 q = 1) (hb : d111947 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d92651, d111947, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d92651, d111947, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d92652 q = 1) (hb : d111948 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d92652, d111948, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92652, d111948, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d92656 q = 1) (hb : d111952 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d92656, d111952, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17579 q ha hb
    | true =>
      simp only [d92656, d111952, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro137 q hb ha
  have h6 (q : Pattern) (ha : d92657 q = 1) (hb : d111953 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d92657, d111953, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92657, d111953, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d92658 q = 1) (hb : d111954 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d92658, d111954, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d92658, d111954, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d92672 q = 1) (hb : d111963 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d92672, d111963, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17582 q ha hb
    | true =>
      simp only [d92672, d111963, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17583 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d92629 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d92673 q = 1) (hb : d111964 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d92673, d111964, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d92673, d111964, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
  have h11 (q : Pattern) (ha : d92678 q = 1) (hb : d111969 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d92678, d111969, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17584 q ha hb
    | true =>
      simp only [d92678, d111969, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d92679 q = 1) (hb : d111970 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d92679, d111970, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d92679, d111970, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d92680 q = 1) (hb : d111971 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d92680, d111971, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d92680, d111971, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d92681 q = 1) (hb : d111972 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d92681, d111972, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d92681, d111972, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d92682 q = 1) (hb : d111973 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d92682, d111973, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d92682, d111973, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d92685 q = 1) (hb : d111976 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d92685, d111976, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17586 q ha hb
    | true =>
      simp only [d92685, d111976, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro141 q hb ha
  have h17 (q : Pattern) (ha : d92686 q = 1) (hb : d111977 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d92686, d111977, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92686, d111977, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d92687 q = 1) (hb : d111978 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d92687, d111978, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d92687, d111978, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h19 (q : Pattern) (ha : d92688 q = 1) (hb : d111979 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d92688, d111979, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92688, d111979, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d92690 q = 1) (hb : d111981 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d92690, d111981, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17587 q ha hb
    | true =>
      simp only [d92690, d111981, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro143 q hb ha
  have h21 (q : Pattern) (ha : d92691 q = 1) (hb : d111982 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d92691, d111982, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92691, d111982, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
  have h22 (q : Pattern) (ha : d92692 q = 1) (hb : d111983 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d92692, d111983, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d92692, d111983, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h23 (q : Pattern) (ha : d92695 q = 1) (hb : d111985 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d92695, d111985, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17588 q ha hb
    | true =>
      simp only [d92695, d111985, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17589 q ha hb
  have h24 (q : Pattern) (ha : d0 q = 1) (hb : d92638 q = 1) : d0 q = 1 := by
    exact ha
  have h25 (q : Pattern) (ha : d92696 q = 1) (hb : d111986 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d92696, d111986, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
    | true =>
      simp only [d92696, d111986, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q hb ha
  have h26 (q : Pattern) (ha : d92698 q = 1) (hb : d111988 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d92698, d111988, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17590 q ha hb
    | true =>
      simp only [d92698, d111988, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h27 (q : Pattern) (ha : d92699 q = 1) (hb : d111989 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d92699, d111989, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h26 q ha hb
    | true =>
      simp only [d92699, d111989, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h28 (q : Pattern) (ha : d92700 q = 1) (hb : d111990 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d92700, d111990, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q ha hb
    | true =>
      simp only [d92700, d111990, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h27 q ha hb
  have h29 (q : Pattern) (ha : d92701 q = 1) (hb : d111991 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d92701, d111991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
    | true =>
      simp only [d92701, d111991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h28 q ha hb
  have h30 (q : Pattern) (ha : d92702 q = 1) (hb : d111992 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d92702, d111992, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d92702, d111992, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h29 q ha hb
  have h31 (q : Pattern) (ha : d92703 q = 1) (hb : d111993 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d92703, d111993, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d92703, d111993, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h30 q ha hb
  exact h31 p ha hb
theorem andIntro17592 (p : Pattern) (ha : d92710 p = 1) (hb : d111995 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d92705 q = 1) (hb : d111925 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d92705, d111925, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17583 q ha hb
    | true =>
      simp only [d92705, d111925, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro107 q hb ha
  have h2 (q : Pattern) (ha : d92706 q = 1) (hb : d111926 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d92706, d111926, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92706, d111926, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d92707 q = 1) (hb : d111927 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d92707, d111927, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d92707, d111927, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d92708 q = 1) (hb : d111928 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d92708, d111928, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92708, d111928, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d92709 q = 1) (hb : d111929 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d92709, d111929, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92709, d111929, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d939 q = 1) (hb : d52558 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d939, d52558, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro107 q ha hb
    | true =>
      simp only [d939, d52558, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d940 q = 1) (hb : d52559 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d940, d52559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d940, d52559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d941 q = 1) (hb : d52560 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d941, d52560, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d941, d52560, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d942 q = 1) (hb : d52561 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d942, d52561, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d942, d52561, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d943 q = 1) (hb : d52562 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d943, d52562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d943, d52562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d92710 q = 1) (hb : d111995 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d92710, d111995, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d92710, d111995, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
  exact h11 p ha hb
theorem andIntro17593 (p : Pattern) (ha : d92717 p = 1) (hb : d112002 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d92695 q = 1) (hb : d111985 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d92695, d111985, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17588 q ha hb
    | true =>
      simp only [d92695, d111985, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17589 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d92638 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d92696 q = 1) (hb : d111986 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d92696, d111986, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d92696, d111986, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d92698 q = 1) (hb : d111988 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d92698, d111988, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17590 q ha hb
    | true =>
      simp only [d92698, d111988, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d92699 q = 1) (hb : d111989 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d92699, d111989, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d92699, d111989, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d92700 q = 1) (hb : d111990 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d92700, d111990, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d92700, d111990, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d92715 q = 1) (hb : d112000 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d92715, d112000, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92715, d112000, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d92716 q = 1) (hb : d112001 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d92716, d112001, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92716, d112001, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d92717 q = 1) (hb : d112002 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d92717, d112002, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92717, d112002, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro17594 (p : Pattern) (ha : d81711 p = 1) (hb : d98938 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d982 q = 1) (hb : d52601 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d982, d52601, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro128 q ha hb
    | true =>
      simp only [d982, d52601, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro115 q ha hb
  have h2 (q : Pattern) (ha : d983 q = 1) (hb : d52602 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d983, d52602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d983, d52602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d984 q = 1) (hb : d52603 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d984, d52603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d984, d52603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d6921 q = 1) (hb : d81709 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d6921, d81709, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d6921, d81709, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d75965 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d81710 q = 1) (hb : d98937 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d81710, d98937, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d81710, d98937, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d81711 q = 1) (hb : d98938 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d81711, d98938, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d81711, d98938, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h7 p ha hb
theorem andIntro17595 (p : Pattern) (ha : d92725 p = 1) (hb : d112009 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d977 q = 1) (hb : d52596 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d977, d52596, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro127 q ha hb
    | true =>
      simp only [d977, d52596, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro128 q ha hb
  have h2 (q : Pattern) (ha : d978 q = 1) (hb : d52597 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d978, d52597, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d978, d52597, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d979 q = 1) (hb : d52598 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d979, d52598, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d979, d52598, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d8689 q = 1) (hb : d92723 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d8689, d92723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d8689, d92723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d81709 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d92724 q = 1) (hb : d112008 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d92724, d112008, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d92724, d112008, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d92725 q = 1) (hb : d112009 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d92725, d112009, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d92725, d112009, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h7 p ha hb
theorem andIntro17596 (p : Pattern) (ha : d92731 p = 1) (hb : d112015 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d92726 q = 1) (hb : d112010 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d92726, d112010, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17595 q ha hb
    | true =>
      simp only [d92726, d112010, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d92727 q = 1) (hb : d112011 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d92727, d112011, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92727, d112011, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d81712 q = 1) (hb : d98939 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d81712, d98939, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17594 q ha hb
    | true =>
      simp only [d81712, d98939, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d81713 q = 1) (hb : d98940 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d81713, d98940, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d81713, d98940, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d92728 q = 1) (hb : d112012 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d92728, d112012, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d92728, d112012, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d92729 q = 1) (hb : d112013 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d92729, d112013, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d92729, d112013, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d92730 q = 1) (hb : d112014 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d92730, d112014, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d92730, d112014, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d92731 q = 1) (hb : d112015 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d92731, d112015, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d92731, d112015, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro17597 (p : Pattern) (ha : d92735 p = 1) (hb : d112019 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d81712 q = 1) (hb : d98939 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d81712, d98939, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17594 q ha hb
    | true =>
      simp only [d81712, d98939, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d81713 q = 1) (hb : d98940 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d81713, d98940, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d81713, d98940, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d1006 q = 1) (hb : d52625 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d1006, d52625, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro117 q ha hb
    | true =>
      simp only [d1006, d52625, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d1007 q = 1) (hb : d52626 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d1007, d52626, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1007, d52626, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d92732 q = 1) (hb : d112016 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d92732, d112016, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d92732, d112016, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d92733 q = 1) (hb : d112017 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d92733, d112017, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d92733, d112017, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d92734 q = 1) (hb : d112018 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d92734, d112018, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d92734, d112018, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d92735 q = 1) (hb : d112019 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d92735, d112019, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d92735, d112019, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro17598 (p : Pattern) (ha : d92738 p = 1) (hb : d98938 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d982 q = 1) (hb : d52601 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d982, d52601, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro128 q ha hb
    | true =>
      simp only [d982, d52601, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro115 q ha hb
  have h2 (q : Pattern) (ha : d983 q = 1) (hb : d52602 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d983, d52602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d983, d52602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d984 q = 1) (hb : d52603 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d984, d52603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d984, d52603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d6921 q = 1) (hb : d81709 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d6921, d81709, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d6921, d81709, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d52614 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d92737 q = 1) (hb : d98937 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d92737, d98937, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d92737, d98937, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d92738 q = 1) (hb : d98938 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d92738, d98938, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d92738, d98938, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h7 p ha hb
theorem andIntro17599 (p : Pattern) (ha : d92750 p = 1) (hb : d112025 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d92739 q = 1) (hb : d98939 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d92739, d98939, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17598 q ha hb
    | true =>
      simp only [d92739, d98939, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d92740 q = 1) (hb : d98940 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d92740, d98940, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92740, d98940, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d92747 q = 1) (hb : d112022 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d92747, d112022, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d92747, d112022, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d92748 q = 1) (hb : d112023 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d92748, d112023, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d92748, d112023, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d92749 q = 1) (hb : d112024 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d92749, d112024, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d92749, d112024, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d92750 q = 1) (hb : d112025 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d92750, d112025, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d92750, d112025, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro17600 (p : Pattern) (ha : d92756 p = 1) (hb : d112031 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d92736 q = 1) (hb : d112020 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d92736, d112020, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17596 q ha hb
    | true =>
      simp only [d92736, d112020, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17597 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d92745 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d92746 q = 1) (hb : d112021 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d92746, d112021, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d92746, d112021, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d92751 q = 1) (hb : d112026 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d92751, d112026, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17599 q ha hb
    | true =>
      simp only [d92751, d112026, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d92752 q = 1) (hb : d112027 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d92752, d112027, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d92752, d112027, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d92753 q = 1) (hb : d112028 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d92753, d112028, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d92753, d112028, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d92754 q = 1) (hb : d112029 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d92754, d112029, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92754, d112029, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d92755 q = 1) (hb : d112030 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d92755, d112030, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92755, d112030, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d92756 q = 1) (hb : d112031 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d92756, d112031, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92756, d112031, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro17601 (p : Pattern) (ha : d92762 p = 1) (hb : d112037 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d92635 q = 1) (hb : d111931 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d92635, d111931, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92635, d111931, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17575 q ha hb
  have h2 (q : Pattern) (ha : d92636 q = 1) (hb : d111932 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d92636, d111932, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d92636, d111932, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d92644 q = 1) (hb : d111940 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d92644, d111940, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17575 q ha hb
    | true =>
      simp only [d92644, d111940, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17577 q ha hb
  have h4 (q : Pattern) (ha : d92645 q = 1) (hb : d111941 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d92645, d111941, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d92645, d111941, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d92646 q = 1) (hb : d111942 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d92646, d111942, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d92646, d111942, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d92704 q = 1) (hb : d111994 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d92704, d111994, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17585 q ha hb
    | true =>
      simp only [d92704, d111994, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17591 q ha hb
  have h7 (q : Pattern) (ha : d92711 q = 1) (hb : d111996 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d92711, d111996, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17592 q ha hb
    | true =>
      simp only [d92711, d111996, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro113 q hb ha
  have h8 (q : Pattern) (ha : d92712 q = 1) (hb : d111997 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d92712, d111997, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d92712, d111997, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d92713 q = 1) (hb : d111998 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d92713, d111998, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d92713, d111998, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h10 (q : Pattern) (ha : d92714 q = 1) (hb : d111999 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d92714, d111999, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d92714, d111999, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d92718 q = 1) (hb : d112003 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d92718, d112003, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92718, d112003, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17593 q ha hb
  have h12 (q : Pattern) (ha : d960 q = 1) (hb : d52579 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d960, d52579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d960, d52579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro114 q ha hb
  have h13 (q : Pattern) (ha : d92719 q = 1) (hb : d112004 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d92719, d112004, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d92719, d112004, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
  have h14 (q : Pattern) (ha : d92720 q = 1) (hb : d112005 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d92720, d112005, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d92720, d112005, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h15 (q : Pattern) (ha : d92721 q = 1) (hb : d112006 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d92721, d112006, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d92721, d112006, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h16 (q : Pattern) (ha : d92722 q = 1) (hb : d112007 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d92722, d112007, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d92722, d112007, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d92757 q = 1) (hb : d112032 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d92757, d112032, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92757, d112032, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17600 q ha hb
  have h18 (q : Pattern) (ha : d1070 q = 1) (hb : d52651 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d1070, d52651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1070, d52651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro119 q ha hb
  have h19 (q : Pattern) (ha : d92758 q = 1) (hb : d112033 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d92758, d112033, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d92758, d112033, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q hb ha
  have h20 (q : Pattern) (ha : d92759 q = 1) (hb : d112034 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d92759, d112034, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d92759, d112034, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h21 (q : Pattern) (ha : d92760 q = 1) (hb : d112035 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d92760, d112035, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d92760, d112035, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h22 (q : Pattern) (ha : d92761 q = 1) (hb : d112036 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d92761, d112036, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d92761, d112036, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h23 (q : Pattern) (ha : d92762 q = 1) (hb : d112037 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d92762, d112037, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d92762, d112037, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
  exact h23 p ha hb
theorem andIntro17602 (p : Pattern) (ha : d92768 p = 1) (hb : d112043 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d92763 q = 1) (hb : d112038 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d92763, d112038, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92763, d112038, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17601 q ha hb
  have h2 (q : Pattern) (ha : d92764 q = 1) (hb : d112039 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d92764, d112039, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92764, d112039, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d92765 q = 1) (hb : d112040 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d92765, d112040, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92765, d112040, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d92766 q = 1) (hb : d112041 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d92766, d112041, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92766, d112041, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d92767 q = 1) (hb : d112042 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d92767, d112042, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92767, d112042, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d92768 q = 1) (hb : d112043 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d92768, d112043, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92768, d112043, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro17603 (p : Pattern) (ha : d92772 p = 1) (hb : d98966 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1129 q = 1) (hb : d52710 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d1129, d52710, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro152 q ha hb
    | true =>
      simp only [d1129, d52710, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro153 q ha hb
  have h2 (q : Pattern) (ha : d1130 q = 1) (hb : d52711 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d1130, d52711, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1130, d52711, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d1131 q = 1) (hb : d52712 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d1131, d52712, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1131, d52712, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d6954 q = 1) (hb : d81742 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d6954, d81742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d6954, d81742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d52727 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d92771 q = 1) (hb : d98965 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d92771, d98965, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d92771, d98965, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d92772 q = 1) (hb : d98966 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d92772, d98966, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d92772, d98966, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h7 p ha hb
theorem andIntro17604 (p : Pattern) (ha : d92778 p = 1) (hb : d112049 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d92773 q = 1) (hb : d98967 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d92773, d98967, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17603 q ha hb
    | true =>
      simp only [d92773, d98967, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d92774 q = 1) (hb : d98968 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d92774, d98968, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92774, d98968, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d1153 q = 1) (hb : d52734 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d1153, d52734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro157 q ha hb
    | true =>
      simp only [d1153, d52734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d1154 q = 1) (hb : d52735 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d1154, d52735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1154, d52735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d92775 q = 1) (hb : d112046 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d92775, d112046, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d92775, d112046, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d92776 q = 1) (hb : d112047 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d92776, d112047, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d92776, d112047, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d92777 q = 1) (hb : d112048 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d92777, d112048, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d92777, d112048, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d92778 q = 1) (hb : d112049 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d92778, d112049, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92778, d112049, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro17605 (p : Pattern) (ha : d92784 p = 1) (hb : d112055 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d92779 q = 1) (hb : d112050 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d92779, d112050, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17604 q ha hb
    | true =>
      simp only [d92779, d112050, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro159 q hb ha
  have h2 (q : Pattern) (ha : d92780 q = 1) (hb : d112051 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d92780, d112051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92780, d112051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d92781 q = 1) (hb : d112052 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d92781, d112052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d92781, d112052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d92782 q = 1) (hb : d112053 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d92782, d112053, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92782, d112053, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d92783 q = 1) (hb : d112054 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d92783, d112054, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92783, d112054, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d92784 q = 1) (hb : d112055 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d92784, d112055, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92784, d112055, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro17606 (p : Pattern) (ha : d92787 p = 1) (hb : d112058 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d92773 q = 1) (hb : d98967 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d92773, d98967, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17603 q ha hb
    | true =>
      simp only [d92773, d98967, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d92774 q = 1) (hb : d98968 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d92774, d98968, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92774, d98968, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d1153 q = 1) (hb : d52734 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d1153, d52734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro157 q ha hb
    | true =>
      simp only [d1153, d52734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d1154 q = 1) (hb : d52735 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d1154, d52735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1154, d52735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d92775 q = 1) (hb : d112046 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d92775, d112046, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d92775, d112046, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d92776 q = 1) (hb : d112047 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d92776, d112047, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d92776, d112047, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d92777 q = 1) (hb : d112048 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d92777, d112048, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d92777, d112048, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d92787 q = 1) (hb : d112058 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d92787, d112058, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d92787, d112058, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro17607 (p : Pattern) (ha : d92793 p = 1) (hb : d112064 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d92779 q = 1) (hb : d112050 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d92779, d112050, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17604 q ha hb
    | true =>
      simp only [d92779, d112050, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro159 q hb ha
  have h2 (q : Pattern) (ha : d92780 q = 1) (hb : d112051 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d92780, d112051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92780, d112051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d92781 q = 1) (hb : d112052 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d92781, d112052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d92781, d112052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d92782 q = 1) (hb : d112053 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d92782, d112053, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92782, d112053, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d92783 q = 1) (hb : d112054 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d92783, d112054, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92783, d112054, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d92788 q = 1) (hb : d112059 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d92788, d112059, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17606 q ha hb
    | true =>
      simp only [d92788, d112059, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro162 q hb ha
  have h7 (q : Pattern) (ha : d92789 q = 1) (hb : d112060 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d92789, d112060, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92789, d112060, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d92790 q = 1) (hb : d112061 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d92790, d112061, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d92790, d112061, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d92791 q = 1) (hb : d112062 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d92791, d112062, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92791, d112062, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d92792 q = 1) (hb : d112063 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d92792, d112063, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92792, d112063, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d92793 q = 1) (hb : d112064 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d92793, d112064, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d92793, d112064, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro17608 (p : Pattern) (ha : d92798 p = 1) (hb : d112069 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d92773 q = 1) (hb : d98967 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d92773, d98967, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17603 q ha hb
    | true =>
      simp only [d92773, d98967, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d92774 q = 1) (hb : d98968 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d92774, d98968, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92774, d98968, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d1153 q = 1) (hb : d52734 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d1153, d52734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro157 q ha hb
    | true =>
      simp only [d1153, d52734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d1154 q = 1) (hb : d52735 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d1154, d52735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1154, d52735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d92775 q = 1) (hb : d112046 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d92775, d112046, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d92775, d112046, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d92776 q = 1) (hb : d112047 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d92776, d112047, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d92776, d112047, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d92797 q = 1) (hb : d112068 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d92797, d112068, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92797, d112068, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d92798 q = 1) (hb : d112069 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d92798, d112069, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92798, d112069, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro17609 (p : Pattern) (ha : d92805 p = 1) (hb : d112076 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d92773 q = 1) (hb : d98967 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d92773, d98967, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17603 q ha hb
    | true =>
      simp only [d92773, d98967, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d92774 q = 1) (hb : d98968 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d92774, d98968, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92774, d98968, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d1153 q = 1) (hb : d52734 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d1153, d52734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro157 q ha hb
    | true =>
      simp only [d1153, d52734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d1154 q = 1) (hb : d52735 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d1154, d52735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1154, d52735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d92775 q = 1) (hb : d112046 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d92775, d112046, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d92775, d112046, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d92803 q = 1) (hb : d112074 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d92803, d112074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92803, d112074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d92804 q = 1) (hb : d112075 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d92804, d112075, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d92804, d112075, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d92805 q = 1) (hb : d112076 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d92805, d112076, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92805, d112076, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro17610 (p : Pattern) (ha : d81744 p = 1) (hb : d98966 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1129 q = 1) (hb : d52710 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d1129, d52710, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro152 q ha hb
    | true =>
      simp only [d1129, d52710, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro153 q ha hb
  have h2 (q : Pattern) (ha : d1130 q = 1) (hb : d52711 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d1130, d52711, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1130, d52711, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d1131 q = 1) (hb : d52712 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d1131, d52712, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1131, d52712, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d6954 q = 1) (hb : d81742 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d6954, d81742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d6954, d81742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d69117 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d81743 q = 1) (hb : d98965 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d81743, d98965, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d81743, d98965, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d81744 q = 1) (hb : d98966 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d81744, d98966, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d81744, d98966, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h7 p ha hb
theorem andIntro17611 (p : Pattern) (ha : d92811 p = 1) (hb : d112081 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1216 q = 1) (hb : d52797 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d1216, d52797, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro175 q ha hb
    | true =>
      simp only [d1216, d52797, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro152 q ha hb
  have h2 (q : Pattern) (ha : d1217 q = 1) (hb : d52798 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d1217, d52798, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1217, d52798, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d1218 q = 1) (hb : d52799 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d1218, d52799, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1218, d52799, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d8780 q = 1) (hb : d92809 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d8780, d92809, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d8780, d92809, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d81742 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d92810 q = 1) (hb : d112080 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d92810, d112080, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d92810, d112080, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d92811 q = 1) (hb : d112081 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d92811, d112081, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d92811, d112081, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h7 p ha hb
theorem andIntro17612 (p : Pattern) (ha : d92817 p = 1) (hb : d112087 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d92812 q = 1) (hb : d112082 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d92812, d112082, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17611 q ha hb
    | true =>
      simp only [d92812, d112082, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d92813 q = 1) (hb : d112083 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d92813, d112083, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92813, d112083, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d81745 q = 1) (hb : d98967 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d81745, d98967, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17610 q ha hb
    | true =>
      simp only [d81745, d98967, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d81746 q = 1) (hb : d98968 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d81746, d98968, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d81746, d98968, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d92814 q = 1) (hb : d112084 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d92814, d112084, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d92814, d112084, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d92815 q = 1) (hb : d112085 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d92815, d112085, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d92815, d112085, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d92816 q = 1) (hb : d112086 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d92816, d112086, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d92816, d112086, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d92817 q = 1) (hb : d112087 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d92817, d112087, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92817, d112087, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro17613 (p : Pattern) (ha : d92821 p = 1) (hb : d112049 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d81745 q = 1) (hb : d98967 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d81745, d98967, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17610 q ha hb
    | true =>
      simp only [d81745, d98967, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d81746 q = 1) (hb : d98968 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d81746, d98968, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d81746, d98968, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d1153 q = 1) (hb : d52734 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d1153, d52734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro157 q ha hb
    | true =>
      simp only [d1153, d52734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d1154 q = 1) (hb : d52735 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d1154, d52735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1154, d52735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d92818 q = 1) (hb : d112046 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d92818, d112046, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d92818, d112046, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d92819 q = 1) (hb : d112047 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d92819, d112047, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d92819, d112047, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d92820 q = 1) (hb : d112048 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d92820, d112048, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d92820, d112048, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d92821 q = 1) (hb : d112049 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d92821, d112049, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92821, d112049, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro17614 (p : Pattern) (ha : d92827 p = 1) (hb : d112093 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d92773 q = 1) (hb : d98967 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d92773, d98967, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17603 q ha hb
    | true =>
      simp only [d92773, d98967, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d92774 q = 1) (hb : d98968 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d92774, d98968, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92774, d98968, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d92824 q = 1) (hb : d112090 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d92824, d112090, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d92824, d112090, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d92825 q = 1) (hb : d112091 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d92825, d112091, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d92825, d112091, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d92826 q = 1) (hb : d112092 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d92826, d112092, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d92826, d112092, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d92827 q = 1) (hb : d112093 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d92827, d112093, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92827, d112093, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro17615 (p : Pattern) (ha : d92833 p = 1) (hb : d112099 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d92799 q = 1) (hb : d112070 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d92799, d112070, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17608 q ha hb
    | true =>
      simp only [d92799, d112070, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro187 q hb ha
  have h2 (q : Pattern) (ha : d92800 q = 1) (hb : d112071 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d92800, d112071, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92800, d112071, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d92801 q = 1) (hb : d112072 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d92801, d112072, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d92801, d112072, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d92802 q = 1) (hb : d112073 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d92802, d112073, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92802, d112073, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d92806 q = 1) (hb : d112077 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d92806, d112077, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17609 q ha hb
    | true =>
      simp only [d92806, d112077, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro189 q hb ha
  have h6 (q : Pattern) (ha : d92807 q = 1) (hb : d112078 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d92807, d112078, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92807, d112078, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d92808 q = 1) (hb : d112079 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d92808, d112079, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d92808, d112079, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d92822 q = 1) (hb : d112088 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d92822, d112088, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17612 q ha hb
    | true =>
      simp only [d92822, d112088, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17613 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d92779 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d92823 q = 1) (hb : d112089 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d92823, d112089, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d92823, d112089, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
  have h11 (q : Pattern) (ha : d92828 q = 1) (hb : d112094 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d92828, d112094, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17614 q ha hb
    | true =>
      simp only [d92828, d112094, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d92829 q = 1) (hb : d112095 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d92829, d112095, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d92829, d112095, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d92830 q = 1) (hb : d112096 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d92830, d112096, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d92830, d112096, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d92831 q = 1) (hb : d112097 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d92831, d112097, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d92831, d112097, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d92832 q = 1) (hb : d112098 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d92832, d112098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d92832, d112098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d92833 q = 1) (hb : d112099 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d92833, d112099, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92833, d112099, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  exact h16 p ha hb
theorem andIntro17616 (p : Pattern) (ha : d92834 p = 1) (hb : d112100 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d92773 q = 1) (hb : d98967 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d92773, d98967, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17603 q ha hb
    | true =>
      simp only [d92773, d98967, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d92774 q = 1) (hb : d98968 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d92774, d98968, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92774, d98968, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d1153 q = 1) (hb : d52734 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d1153, d52734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro157 q ha hb
    | true =>
      simp only [d1153, d52734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d1154 q = 1) (hb : d52735 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d1154, d52735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1154, d52735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d92775 q = 1) (hb : d112046 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d92775, d112046, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d92775, d112046, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d92776 q = 1) (hb : d112047 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d92776, d112047, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d92776, d112047, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d92797 q = 1) (hb : d112068 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d92797, d112068, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92797, d112068, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d92834 q = 1) (hb : d112100 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d92834, d112100, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d92834, d112100, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro17617 (p : Pattern) (ha : d92839 p = 1) (hb : d112105 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d92773 q = 1) (hb : d98967 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d92773, d98967, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17603 q ha hb
    | true =>
      simp only [d92773, d98967, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d92774 q = 1) (hb : d98968 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d92774, d98968, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92774, d98968, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d1153 q = 1) (hb : d52734 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d1153, d52734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro157 q ha hb
    | true =>
      simp only [d1153, d52734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d1154 q = 1) (hb : d52735 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d1154, d52735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1154, d52735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d92775 q = 1) (hb : d112046 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d92775, d112046, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d92775, d112046, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d92803 q = 1) (hb : d112074 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d92803, d112074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92803, d112074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d92804 q = 1) (hb : d112075 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d92804, d112075, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d92804, d112075, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d92839 q = 1) (hb : d112105 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d92839, d112105, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d92839, d112105, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro17618 (p : Pattern) (ha : d92843 p = 1) (hb : d112109 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d92812 q = 1) (hb : d112082 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d92812, d112082, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17611 q ha hb
    | true =>
      simp only [d92812, d112082, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d92813 q = 1) (hb : d112083 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d92813, d112083, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92813, d112083, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d81745 q = 1) (hb : d98967 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d81745, d98967, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17610 q ha hb
    | true =>
      simp only [d81745, d98967, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d81746 q = 1) (hb : d98968 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d81746, d98968, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d81746, d98968, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d92814 q = 1) (hb : d112084 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d92814, d112084, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d92814, d112084, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d92815 q = 1) (hb : d112085 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d92815, d112085, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d92815, d112085, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d92816 q = 1) (hb : d112086 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d92816, d112086, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d92816, d112086, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d92843 q = 1) (hb : d112109 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d92843, d112109, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d92843, d112109, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro17619 (p : Pattern) (ha : d92844 p = 1) (hb : d112058 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d81745 q = 1) (hb : d98967 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d81745, d98967, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17610 q ha hb
    | true =>
      simp only [d81745, d98967, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d81746 q = 1) (hb : d98968 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d81746, d98968, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d81746, d98968, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d1153 q = 1) (hb : d52734 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d1153, d52734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro157 q ha hb
    | true =>
      simp only [d1153, d52734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d1154 q = 1) (hb : d52735 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d1154, d52735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1154, d52735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d92818 q = 1) (hb : d112046 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d92818, d112046, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d92818, d112046, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d92819 q = 1) (hb : d112047 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d92819, d112047, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d92819, d112047, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d92820 q = 1) (hb : d112048 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d92820, d112048, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d92820, d112048, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d92844 q = 1) (hb : d112058 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d92844, d112058, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d92844, d112058, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro17620 (p : Pattern) (ha : d92847 p = 1) (hb : d112112 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d92773 q = 1) (hb : d98967 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d92773, d98967, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17603 q ha hb
    | true =>
      simp only [d92773, d98967, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d92774 q = 1) (hb : d98968 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d92774, d98968, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92774, d98968, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d92824 q = 1) (hb : d112090 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d92824, d112090, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d92824, d112090, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d92825 q = 1) (hb : d112091 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d92825, d112091, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d92825, d112091, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d92826 q = 1) (hb : d112092 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d92826, d112092, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d92826, d112092, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d92847 q = 1) (hb : d112112 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d92847, d112112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d92847, d112112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro17621 (p : Pattern) (ha : d92853 p = 1) (hb : d112118 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d92799 q = 1) (hb : d112070 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d92799, d112070, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17608 q ha hb
    | true =>
      simp only [d92799, d112070, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro187 q hb ha
  have h2 (q : Pattern) (ha : d92800 q = 1) (hb : d112071 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d92800, d112071, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92800, d112071, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d92801 q = 1) (hb : d112072 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d92801, d112072, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d92801, d112072, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d92802 q = 1) (hb : d112073 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d92802, d112073, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92802, d112073, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d92806 q = 1) (hb : d112077 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d92806, d112077, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17609 q ha hb
    | true =>
      simp only [d92806, d112077, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro189 q hb ha
  have h6 (q : Pattern) (ha : d92807 q = 1) (hb : d112078 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d92807, d112078, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92807, d112078, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d92808 q = 1) (hb : d112079 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d92808, d112079, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d92808, d112079, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d92822 q = 1) (hb : d112088 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d92822, d112088, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17612 q ha hb
    | true =>
      simp only [d92822, d112088, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17613 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d92779 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d92823 q = 1) (hb : d112089 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d92823, d112089, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d92823, d112089, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
  have h11 (q : Pattern) (ha : d92828 q = 1) (hb : d112094 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d92828, d112094, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17614 q ha hb
    | true =>
      simp only [d92828, d112094, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d92829 q = 1) (hb : d112095 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d92829, d112095, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d92829, d112095, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d92830 q = 1) (hb : d112096 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d92830, d112096, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d92830, d112096, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d92831 q = 1) (hb : d112097 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d92831, d112097, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d92831, d112097, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d92832 q = 1) (hb : d112098 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d92832, d112098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d92832, d112098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d92835 q = 1) (hb : d112101 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d92835, d112101, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17616 q ha hb
    | true =>
      simp only [d92835, d112101, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro193 q hb ha
  have h17 (q : Pattern) (ha : d92836 q = 1) (hb : d112102 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d92836, d112102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92836, d112102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d92837 q = 1) (hb : d112103 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d92837, d112103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d92837, d112103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h19 (q : Pattern) (ha : d92838 q = 1) (hb : d112104 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d92838, d112104, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92838, d112104, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d92840 q = 1) (hb : d112106 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d92840, d112106, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17617 q ha hb
    | true =>
      simp only [d92840, d112106, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro195 q hb ha
  have h21 (q : Pattern) (ha : d92841 q = 1) (hb : d112107 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d92841, d112107, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92841, d112107, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
  have h22 (q : Pattern) (ha : d92842 q = 1) (hb : d112108 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d92842, d112108, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d92842, d112108, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h23 (q : Pattern) (ha : d92845 q = 1) (hb : d112110 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d92845, d112110, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17618 q ha hb
    | true =>
      simp only [d92845, d112110, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17619 q ha hb
  have h24 (q : Pattern) (ha : d0 q = 1) (hb : d92788 q = 1) : d0 q = 1 := by
    exact ha
  have h25 (q : Pattern) (ha : d92846 q = 1) (hb : d112111 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d92846, d112111, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
    | true =>
      simp only [d92846, d112111, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q hb ha
  have h26 (q : Pattern) (ha : d92848 q = 1) (hb : d112113 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d92848, d112113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17620 q ha hb
    | true =>
      simp only [d92848, d112113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h27 (q : Pattern) (ha : d92849 q = 1) (hb : d112114 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d92849, d112114, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h26 q ha hb
    | true =>
      simp only [d92849, d112114, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h28 (q : Pattern) (ha : d92850 q = 1) (hb : d112115 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d92850, d112115, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q ha hb
    | true =>
      simp only [d92850, d112115, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h27 q ha hb
  have h29 (q : Pattern) (ha : d92851 q = 1) (hb : d112116 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d92851, d112116, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
    | true =>
      simp only [d92851, d112116, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h28 q ha hb
  have h30 (q : Pattern) (ha : d92852 q = 1) (hb : d112117 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d92852, d112117, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d92852, d112117, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h29 q ha hb
  have h31 (q : Pattern) (ha : d92853 q = 1) (hb : d112118 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d92853, d112118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d92853, d112118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h30 q ha hb
  exact h31 p ha hb
theorem andIntro17622 (p : Pattern) (ha : d92860 p = 1) (hb : d112120 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d92855 q = 1) (hb : d112050 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d92855, d112050, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17613 q ha hb
    | true =>
      simp only [d92855, d112050, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro159 q hb ha
  have h2 (q : Pattern) (ha : d92856 q = 1) (hb : d112051 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d92856, d112051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92856, d112051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d92857 q = 1) (hb : d112052 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d92857, d112052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d92857, d112052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d92858 q = 1) (hb : d112053 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d92858, d112053, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92858, d112053, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d92859 q = 1) (hb : d112054 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d92859, d112054, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92859, d112054, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d1350 q = 1) (hb : d52838 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d1350, d52838, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro159 q ha hb
    | true =>
      simp only [d1350, d52838, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d1351 q = 1) (hb : d52839 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d1351, d52839, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1351, d52839, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d1352 q = 1) (hb : d52840 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d1352, d52840, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d1352, d52840, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d1353 q = 1) (hb : d52841 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d1353, d52841, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1353, d52841, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d1354 q = 1) (hb : d52842 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d1354, d52842, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1354, d52842, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d92860 q = 1) (hb : d112120 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d92860, d112120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d92860, d112120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
  exact h11 p ha hb
theorem andIntro17623 (p : Pattern) (ha : d92867 p = 1) (hb : d112127 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d92845 q = 1) (hb : d112110 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d92845, d112110, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17618 q ha hb
    | true =>
      simp only [d92845, d112110, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17619 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d92788 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d92846 q = 1) (hb : d112111 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d92846, d112111, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d92846, d112111, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d92848 q = 1) (hb : d112113 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d92848, d112113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17620 q ha hb
    | true =>
      simp only [d92848, d112113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d92849 q = 1) (hb : d112114 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d92849, d112114, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d92849, d112114, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d92850 q = 1) (hb : d112115 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d92850, d112115, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d92850, d112115, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d92865 q = 1) (hb : d112125 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d92865, d112125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92865, d112125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d92866 q = 1) (hb : d112126 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d92866, d112126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92866, d112126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d92867 q = 1) (hb : d112127 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d92867, d112127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92867, d112127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro17624 (p : Pattern) (ha : d81790 p = 1) (hb : d98999 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1402 q = 1) (hb : d52890 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d1402, d52890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro180 q ha hb
    | true =>
      simp only [d1402, d52890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro167 q ha hb
  have h2 (q : Pattern) (ha : d1403 q = 1) (hb : d52891 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d1403, d52891, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1403, d52891, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d1404 q = 1) (hb : d52892 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d1404, d52892, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1404, d52892, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d7000 q = 1) (hb : d81788 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d7000, d81788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d7000, d81788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d76099 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d81789 q = 1) (hb : d98998 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d81789, d98998, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d81789, d98998, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d81790 q = 1) (hb : d98999 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d81790, d98999, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d81790, d98999, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h7 p ha hb
theorem andIntro17625 (p : Pattern) (ha : d92875 p = 1) (hb : d112134 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1397 q = 1) (hb : d52885 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d1397, d52885, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro179 q ha hb
    | true =>
      simp only [d1397, d52885, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro180 q ha hb
  have h2 (q : Pattern) (ha : d1398 q = 1) (hb : d52886 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d1398, d52886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1398, d52886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d1399 q = 1) (hb : d52887 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d1399, d52887, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1399, d52887, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d8856 q = 1) (hb : d92873 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d8856, d92873, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d8856, d92873, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d81788 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d92874 q = 1) (hb : d112133 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d92874, d112133, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d92874, d112133, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d92875 q = 1) (hb : d112134 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d92875, d112134, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d92875, d112134, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h7 p ha hb
theorem andIntro17626 (p : Pattern) (ha : d92881 p = 1) (hb : d112140 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d92876 q = 1) (hb : d112135 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d92876, d112135, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17625 q ha hb
    | true =>
      simp only [d92876, d112135, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d92877 q = 1) (hb : d112136 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d92877, d112136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92877, d112136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d81791 q = 1) (hb : d99000 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d81791, d99000, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17624 q ha hb
    | true =>
      simp only [d81791, d99000, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d81792 q = 1) (hb : d99001 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d81792, d99001, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d81792, d99001, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d92878 q = 1) (hb : d112137 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d92878, d112137, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d92878, d112137, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d92879 q = 1) (hb : d112138 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d92879, d112138, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d92879, d112138, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d92880 q = 1) (hb : d112139 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d92880, d112139, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d92880, d112139, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d92881 q = 1) (hb : d112140 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d92881, d112140, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d92881, d112140, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro17627 (p : Pattern) (ha : d92885 p = 1) (hb : d112144 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d81791 q = 1) (hb : d99000 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d81791, d99000, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17624 q ha hb
    | true =>
      simp only [d81791, d99000, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d81792 q = 1) (hb : d99001 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d81792, d99001, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d81792, d99001, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d1431 q = 1) (hb : d52919 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d1431, d52919, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro169 q ha hb
    | true =>
      simp only [d1431, d52919, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d1432 q = 1) (hb : d52920 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d1432, d52920, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1432, d52920, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d92882 q = 1) (hb : d112141 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d92882, d112141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d92882, d112141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d92883 q = 1) (hb : d112142 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d92883, d112142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d92883, d112142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d92884 q = 1) (hb : d112143 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d92884, d112143, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d92884, d112143, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d92885 q = 1) (hb : d112144 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d92885, d112144, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d92885, d112144, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro17628 (p : Pattern) (ha : d92888 p = 1) (hb : d98999 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1402 q = 1) (hb : d52890 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d1402, d52890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro180 q ha hb
    | true =>
      simp only [d1402, d52890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro167 q ha hb
  have h2 (q : Pattern) (ha : d1403 q = 1) (hb : d52891 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d1403, d52891, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1403, d52891, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d1404 q = 1) (hb : d52892 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d1404, d52892, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1404, d52892, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d7000 q = 1) (hb : d81788 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d7000, d81788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d7000, d81788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d52908 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d92887 q = 1) (hb : d98998 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d92887, d98998, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d92887, d98998, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d92888 q = 1) (hb : d98999 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d92888, d98999, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d92888, d98999, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h7 p ha hb
theorem andIntro17629 (p : Pattern) (ha : d92900 p = 1) (hb : d112150 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d92889 q = 1) (hb : d99000 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d92889, d99000, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17628 q ha hb
    | true =>
      simp only [d92889, d99000, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d92890 q = 1) (hb : d99001 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d92890, d99001, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92890, d99001, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d92897 q = 1) (hb : d112147 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d92897, d112147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d92897, d112147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d92898 q = 1) (hb : d112148 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d92898, d112148, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d92898, d112148, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d92899 q = 1) (hb : d112149 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d92899, d112149, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d92899, d112149, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d92900 q = 1) (hb : d112150 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d92900, d112150, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d92900, d112150, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro17630 (p : Pattern) (ha : d92906 p = 1) (hb : d112156 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d92886 q = 1) (hb : d112145 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d92886, d112145, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17626 q ha hb
    | true =>
      simp only [d92886, d112145, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17627 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d92895 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d92896 q = 1) (hb : d112146 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d92896, d112146, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d92896, d112146, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d92901 q = 1) (hb : d112151 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d92901, d112151, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17629 q ha hb
    | true =>
      simp only [d92901, d112151, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d92902 q = 1) (hb : d112152 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d92902, d112152, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d92902, d112152, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d92903 q = 1) (hb : d112153 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d92903, d112153, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d92903, d112153, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d92904 q = 1) (hb : d112154 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d92904, d112154, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92904, d112154, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d92905 q = 1) (hb : d112155 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d92905, d112155, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92905, d112155, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d92906 q = 1) (hb : d112156 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d92906, d112156, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92906, d112156, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro17631 (p : Pattern) (ha : d92912 p = 1) (hb : d112162 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d92785 q = 1) (hb : d112056 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d92785, d112056, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92785, d112056, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17605 q ha hb
  have h2 (q : Pattern) (ha : d92786 q = 1) (hb : d112057 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d92786, d112057, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d92786, d112057, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d92794 q = 1) (hb : d112065 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d92794, d112065, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17605 q ha hb
    | true =>
      simp only [d92794, d112065, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17607 q ha hb
  have h4 (q : Pattern) (ha : d92795 q = 1) (hb : d112066 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d92795, d112066, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d92795, d112066, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d92796 q = 1) (hb : d112067 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d92796, d112067, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d92796, d112067, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d92854 q = 1) (hb : d112119 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d92854, d112119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17615 q ha hb
    | true =>
      simp only [d92854, d112119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17621 q ha hb
  have h7 (q : Pattern) (ha : d92861 q = 1) (hb : d112121 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d92861, d112121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17622 q ha hb
    | true =>
      simp only [d92861, d112121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro165 q hb ha
  have h8 (q : Pattern) (ha : d92862 q = 1) (hb : d112122 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d92862, d112122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d92862, d112122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d92863 q = 1) (hb : d112123 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d92863, d112123, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d92863, d112123, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h10 (q : Pattern) (ha : d92864 q = 1) (hb : d112124 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d92864, d112124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d92864, d112124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d92868 q = 1) (hb : d112128 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d92868, d112128, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92868, d112128, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17623 q ha hb
  have h12 (q : Pattern) (ha : d1371 q = 1) (hb : d52859 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d1371, d52859, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1371, d52859, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro166 q ha hb
  have h13 (q : Pattern) (ha : d92869 q = 1) (hb : d112129 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d92869, d112129, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d92869, d112129, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
  have h14 (q : Pattern) (ha : d92870 q = 1) (hb : d112130 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d92870, d112130, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d92870, d112130, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h15 (q : Pattern) (ha : d92871 q = 1) (hb : d112131 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d92871, d112131, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d92871, d112131, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h16 (q : Pattern) (ha : d92872 q = 1) (hb : d112132 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d92872, d112132, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d92872, d112132, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d92907 q = 1) (hb : d112157 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d92907, d112157, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92907, d112157, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17630 q ha hb
  have h18 (q : Pattern) (ha : d1504 q = 1) (hb : d52945 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d1504, d52945, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1504, d52945, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro171 q ha hb
  have h19 (q : Pattern) (ha : d92908 q = 1) (hb : d112158 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d92908, d112158, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d92908, d112158, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q hb ha
  have h20 (q : Pattern) (ha : d92909 q = 1) (hb : d112159 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d92909, d112159, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d92909, d112159, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h21 (q : Pattern) (ha : d92910 q = 1) (hb : d112160 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d92910, d112160, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d92910, d112160, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h22 (q : Pattern) (ha : d92911 q = 1) (hb : d112161 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d92911, d112161, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d92911, d112161, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h23 (q : Pattern) (ha : d92912 q = 1) (hb : d112162 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d92912, d112162, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d92912, d112162, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
  exact h23 p ha hb
theorem andIntro17632 (p : Pattern) (ha : d92918 p = 1) (hb : d112168 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d92913 q = 1) (hb : d112163 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d92913, d112163, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92913, d112163, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17631 q ha hb
  have h2 (q : Pattern) (ha : d92914 q = 1) (hb : d112164 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d92914, d112164, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92914, d112164, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d92915 q = 1) (hb : d112165 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d92915, d112165, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92915, d112165, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d92916 q = 1) (hb : d112166 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d92916, d112166, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92916, d112166, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d92917 q = 1) (hb : d112167 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d92917, d112167, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92917, d112167, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d92918 q = 1) (hb : d112168 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d92918, d112168, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92918, d112168, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro17633 (p : Pattern) (ha : d92923 p = 1) (hb : d99028 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1590 q = 1) (hb : d53031 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d1590, d53031, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro210 q ha hb
    | true =>
      simp only [d1590, d53031, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro211 q ha hb
  have h2 (q : Pattern) (ha : d1591 q = 1) (hb : d53032 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d1591, d53032, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1591, d53032, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d1592 q = 1) (hb : d53033 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d1592, d53033, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1592, d53033, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d7034 q = 1) (hb : d81822 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d7034, d81822, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d7034, d81822, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d53048 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d92922 q = 1) (hb : d99027 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d92922, d99027, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d92922, d99027, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d92923 q = 1) (hb : d99028 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d92923, d99028, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d92923, d99028, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h7 p ha hb
theorem andIntro17634 (p : Pattern) (ha : d92929 p = 1) (hb : d112175 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d92924 q = 1) (hb : d99029 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d92924, d99029, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17633 q ha hb
    | true =>
      simp only [d92924, d99029, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d92925 q = 1) (hb : d99030 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d92925, d99030, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92925, d99030, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d1614 q = 1) (hb : d53055 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d1614, d53055, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro215 q ha hb
    | true =>
      simp only [d1614, d53055, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d1615 q = 1) (hb : d53056 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d1615, d53056, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1615, d53056, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d92926 q = 1) (hb : d112172 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d92926, d112172, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d92926, d112172, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d92927 q = 1) (hb : d112173 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d92927, d112173, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d92927, d112173, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d92928 q = 1) (hb : d112174 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d92928, d112174, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d92928, d112174, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d92929 q = 1) (hb : d112175 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d92929, d112175, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92929, d112175, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro17635 (p : Pattern) (ha : d92935 p = 1) (hb : d112181 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d92930 q = 1) (hb : d112176 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d92930, d112176, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17634 q ha hb
    | true =>
      simp only [d92930, d112176, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro217 q hb ha
  have h2 (q : Pattern) (ha : d92931 q = 1) (hb : d112177 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d92931, d112177, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92931, d112177, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d92932 q = 1) (hb : d112178 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d92932, d112178, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d92932, d112178, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d92933 q = 1) (hb : d112179 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d92933, d112179, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92933, d112179, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d92934 q = 1) (hb : d112180 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d92934, d112180, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92934, d112180, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d92935 q = 1) (hb : d112181 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d92935, d112181, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92935, d112181, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro17636 (p : Pattern) (ha : d92938 p = 1) (hb : d112184 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d92924 q = 1) (hb : d99029 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d92924, d99029, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17633 q ha hb
    | true =>
      simp only [d92924, d99029, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d92925 q = 1) (hb : d99030 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d92925, d99030, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92925, d99030, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d1614 q = 1) (hb : d53055 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d1614, d53055, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro215 q ha hb
    | true =>
      simp only [d1614, d53055, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d1615 q = 1) (hb : d53056 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d1615, d53056, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1615, d53056, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d92926 q = 1) (hb : d112172 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d92926, d112172, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d92926, d112172, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d92927 q = 1) (hb : d112173 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d92927, d112173, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d92927, d112173, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d92928 q = 1) (hb : d112174 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d92928, d112174, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d92928, d112174, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d92938 q = 1) (hb : d112184 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d92938, d112184, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d92938, d112184, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro17637 (p : Pattern) (ha : d92944 p = 1) (hb : d112190 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d92930 q = 1) (hb : d112176 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d92930, d112176, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17634 q ha hb
    | true =>
      simp only [d92930, d112176, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro217 q hb ha
  have h2 (q : Pattern) (ha : d92931 q = 1) (hb : d112177 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d92931, d112177, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92931, d112177, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d92932 q = 1) (hb : d112178 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d92932, d112178, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d92932, d112178, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d92933 q = 1) (hb : d112179 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d92933, d112179, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92933, d112179, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d92934 q = 1) (hb : d112180 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d92934, d112180, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92934, d112180, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d92939 q = 1) (hb : d112185 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d92939, d112185, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17636 q ha hb
    | true =>
      simp only [d92939, d112185, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro220 q hb ha
  have h7 (q : Pattern) (ha : d92940 q = 1) (hb : d112186 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d92940, d112186, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92940, d112186, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d92941 q = 1) (hb : d112187 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d92941, d112187, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d92941, d112187, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d92942 q = 1) (hb : d112188 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d92942, d112188, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92942, d112188, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d92943 q = 1) (hb : d112189 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d92943, d112189, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92943, d112189, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d92944 q = 1) (hb : d112190 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d92944, d112190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d92944, d112190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro17638 (p : Pattern) (ha : d92949 p = 1) (hb : d112195 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d92924 q = 1) (hb : d99029 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d92924, d99029, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17633 q ha hb
    | true =>
      simp only [d92924, d99029, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d92925 q = 1) (hb : d99030 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d92925, d99030, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92925, d99030, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d1614 q = 1) (hb : d53055 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d1614, d53055, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro215 q ha hb
    | true =>
      simp only [d1614, d53055, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d1615 q = 1) (hb : d53056 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d1615, d53056, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1615, d53056, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d92926 q = 1) (hb : d112172 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d92926, d112172, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d92926, d112172, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d92927 q = 1) (hb : d112173 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d92927, d112173, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d92927, d112173, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d92948 q = 1) (hb : d112194 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d92948, d112194, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92948, d112194, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d92949 q = 1) (hb : d112195 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d92949, d112195, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92949, d112195, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro17639 (p : Pattern) (ha : d92956 p = 1) (hb : d112202 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d92924 q = 1) (hb : d99029 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d92924, d99029, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17633 q ha hb
    | true =>
      simp only [d92924, d99029, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d92925 q = 1) (hb : d99030 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d92925, d99030, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92925, d99030, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d1614 q = 1) (hb : d53055 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d1614, d53055, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro215 q ha hb
    | true =>
      simp only [d1614, d53055, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d1615 q = 1) (hb : d53056 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d1615, d53056, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1615, d53056, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d92926 q = 1) (hb : d112172 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d92926, d112172, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d92926, d112172, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d92954 q = 1) (hb : d112200 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d92954, d112200, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92954, d112200, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d92955 q = 1) (hb : d112201 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d92955, d112201, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d92955, d112201, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d92956 q = 1) (hb : d112202 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d92956, d112202, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92956, d112202, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro17640 (p : Pattern) (ha : d81824 p = 1) (hb : d99028 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1590 q = 1) (hb : d53031 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d1590, d53031, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro210 q ha hb
    | true =>
      simp only [d1590, d53031, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro211 q ha hb
  have h2 (q : Pattern) (ha : d1591 q = 1) (hb : d53032 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d1591, d53032, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1591, d53032, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d1592 q = 1) (hb : d53033 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d1592, d53033, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1592, d53033, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d7034 q = 1) (hb : d81822 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d7034, d81822, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d7034, d81822, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d69230 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d81823 q = 1) (hb : d99027 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d81823, d99027, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d81823, d99027, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d81824 q = 1) (hb : d99028 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d81824, d99028, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d81824, d99028, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h7 p ha hb
theorem andIntro17641 (p : Pattern) (ha : d92962 p = 1) (hb : d112207 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1671 q = 1) (hb : d53112 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d1671, d53112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro231 q ha hb
    | true =>
      simp only [d1671, d53112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro210 q ha hb
  have h2 (q : Pattern) (ha : d1672 q = 1) (hb : d53113 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d1672, d53113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1672, d53113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d1673 q = 1) (hb : d53114 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d1673, d53114, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1673, d53114, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d8948 q = 1) (hb : d92960 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d8948, d92960, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d8948, d92960, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d81822 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d92961 q = 1) (hb : d112206 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d92961, d112206, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d92961, d112206, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d92962 q = 1) (hb : d112207 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d92962, d112207, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d92962, d112207, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h7 p ha hb
theorem andIntro17642 (p : Pattern) (ha : d92968 p = 1) (hb : d112213 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d92963 q = 1) (hb : d112208 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d92963, d112208, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17641 q ha hb
    | true =>
      simp only [d92963, d112208, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d92964 q = 1) (hb : d112209 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d92964, d112209, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92964, d112209, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d81825 q = 1) (hb : d99029 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d81825, d99029, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17640 q ha hb
    | true =>
      simp only [d81825, d99029, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d81826 q = 1) (hb : d99030 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d81826, d99030, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d81826, d99030, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d92965 q = 1) (hb : d112210 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d92965, d112210, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d92965, d112210, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d92966 q = 1) (hb : d112211 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d92966, d112211, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d92966, d112211, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d92967 q = 1) (hb : d112212 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d92967, d112212, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d92967, d112212, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d92968 q = 1) (hb : d112213 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d92968, d112213, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92968, d112213, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro17643 (p : Pattern) (ha : d92972 p = 1) (hb : d112175 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d81825 q = 1) (hb : d99029 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d81825, d99029, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17640 q ha hb
    | true =>
      simp only [d81825, d99029, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d81826 q = 1) (hb : d99030 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d81826, d99030, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d81826, d99030, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d1614 q = 1) (hb : d53055 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d1614, d53055, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro215 q ha hb
    | true =>
      simp only [d1614, d53055, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d1615 q = 1) (hb : d53056 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d1615, d53056, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1615, d53056, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d92969 q = 1) (hb : d112172 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d92969, d112172, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d92969, d112172, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d92970 q = 1) (hb : d112173 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d92970, d112173, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d92970, d112173, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d92971 q = 1) (hb : d112174 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d92971, d112174, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d92971, d112174, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d92972 q = 1) (hb : d112175 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d92972, d112175, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92972, d112175, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro17644 (p : Pattern) (ha : d92978 p = 1) (hb : d112219 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d92924 q = 1) (hb : d99029 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d92924, d99029, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17633 q ha hb
    | true =>
      simp only [d92924, d99029, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d92925 q = 1) (hb : d99030 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d92925, d99030, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92925, d99030, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d92975 q = 1) (hb : d112216 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d92975, d112216, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d92975, d112216, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d92976 q = 1) (hb : d112217 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d92976, d112217, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d92976, d112217, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d92977 q = 1) (hb : d112218 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d92977, d112218, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d92977, d112218, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d92978 q = 1) (hb : d112219 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d92978, d112219, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92978, d112219, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro17645 (p : Pattern) (ha : d92984 p = 1) (hb : d112225 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d92950 q = 1) (hb : d112196 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d92950, d112196, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17638 q ha hb
    | true =>
      simp only [d92950, d112196, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro243 q hb ha
  have h2 (q : Pattern) (ha : d92951 q = 1) (hb : d112197 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d92951, d112197, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92951, d112197, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d92952 q = 1) (hb : d112198 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d92952, d112198, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d92952, d112198, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d92953 q = 1) (hb : d112199 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d92953, d112199, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92953, d112199, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d92957 q = 1) (hb : d112203 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d92957, d112203, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17639 q ha hb
    | true =>
      simp only [d92957, d112203, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro245 q hb ha
  have h6 (q : Pattern) (ha : d92958 q = 1) (hb : d112204 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d92958, d112204, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92958, d112204, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d92959 q = 1) (hb : d112205 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d92959, d112205, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d92959, d112205, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d92973 q = 1) (hb : d112214 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d92973, d112214, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17642 q ha hb
    | true =>
      simp only [d92973, d112214, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17643 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d92930 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d92974 q = 1) (hb : d112215 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d92974, d112215, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d92974, d112215, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
  have h11 (q : Pattern) (ha : d92979 q = 1) (hb : d112220 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d92979, d112220, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17644 q ha hb
    | true =>
      simp only [d92979, d112220, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d92980 q = 1) (hb : d112221 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d92980, d112221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d92980, d112221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d92981 q = 1) (hb : d112222 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d92981, d112222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d92981, d112222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d92982 q = 1) (hb : d112223 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d92982, d112223, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d92982, d112223, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d92983 q = 1) (hb : d112224 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d92983, d112224, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d92983, d112224, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d92984 q = 1) (hb : d112225 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d92984, d112225, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92984, d112225, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  exact h16 p ha hb
theorem andIntro17646 (p : Pattern) (ha : d92985 p = 1) (hb : d112226 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d92924 q = 1) (hb : d99029 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d92924, d99029, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17633 q ha hb
    | true =>
      simp only [d92924, d99029, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d92925 q = 1) (hb : d99030 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d92925, d99030, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92925, d99030, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d1614 q = 1) (hb : d53055 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d1614, d53055, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro215 q ha hb
    | true =>
      simp only [d1614, d53055, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d1615 q = 1) (hb : d53056 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d1615, d53056, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1615, d53056, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d92926 q = 1) (hb : d112172 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d92926, d112172, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d92926, d112172, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d92927 q = 1) (hb : d112173 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d92927, d112173, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d92927, d112173, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d92948 q = 1) (hb : d112194 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d92948, d112194, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92948, d112194, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d92985 q = 1) (hb : d112226 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d92985, d112226, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d92985, d112226, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro17647 (p : Pattern) (ha : d92990 p = 1) (hb : d112231 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d92924 q = 1) (hb : d99029 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d92924, d99029, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17633 q ha hb
    | true =>
      simp only [d92924, d99029, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d92925 q = 1) (hb : d99030 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d92925, d99030, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92925, d99030, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d1614 q = 1) (hb : d53055 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d1614, d53055, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro215 q ha hb
    | true =>
      simp only [d1614, d53055, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d1615 q = 1) (hb : d53056 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d1615, d53056, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1615, d53056, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d92926 q = 1) (hb : d112172 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d92926, d112172, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d92926, d112172, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d92954 q = 1) (hb : d112200 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d92954, d112200, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92954, d112200, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d92955 q = 1) (hb : d112201 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d92955, d112201, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d92955, d112201, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d92990 q = 1) (hb : d112231 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d92990, d112231, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d92990, d112231, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro17648 (p : Pattern) (ha : d92994 p = 1) (hb : d112235 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d92963 q = 1) (hb : d112208 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d92963, d112208, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17641 q ha hb
    | true =>
      simp only [d92963, d112208, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d92964 q = 1) (hb : d112209 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d92964, d112209, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92964, d112209, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d81825 q = 1) (hb : d99029 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d81825, d99029, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17640 q ha hb
    | true =>
      simp only [d81825, d99029, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d81826 q = 1) (hb : d99030 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d81826, d99030, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d81826, d99030, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d92965 q = 1) (hb : d112210 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d92965, d112210, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d92965, d112210, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d92966 q = 1) (hb : d112211 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d92966, d112211, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d92966, d112211, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d92967 q = 1) (hb : d112212 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d92967, d112212, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d92967, d112212, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d92994 q = 1) (hb : d112235 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d92994, d112235, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d92994, d112235, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro17649 (p : Pattern) (ha : d92995 p = 1) (hb : d112184 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d81825 q = 1) (hb : d99029 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d81825, d99029, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17640 q ha hb
    | true =>
      simp only [d81825, d99029, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d81826 q = 1) (hb : d99030 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d81826, d99030, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d81826, d99030, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d1614 q = 1) (hb : d53055 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d1614, d53055, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro215 q ha hb
    | true =>
      simp only [d1614, d53055, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d1615 q = 1) (hb : d53056 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d1615, d53056, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1615, d53056, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d92969 q = 1) (hb : d112172 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d92969, d112172, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d92969, d112172, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d92970 q = 1) (hb : d112173 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d92970, d112173, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d92970, d112173, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d92971 q = 1) (hb : d112174 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d92971, d112174, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d92971, d112174, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d92995 q = 1) (hb : d112184 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d92995, d112184, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d92995, d112184, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro17650 (p : Pattern) (ha : d92998 p = 1) (hb : d112238 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d92924 q = 1) (hb : d99029 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d92924, d99029, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17633 q ha hb
    | true =>
      simp only [d92924, d99029, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d92925 q = 1) (hb : d99030 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d92925, d99030, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92925, d99030, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d92975 q = 1) (hb : d112216 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d92975, d112216, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d92975, d112216, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d92976 q = 1) (hb : d112217 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d92976, d112217, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d92976, d112217, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d92977 q = 1) (hb : d112218 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d92977, d112218, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d92977, d112218, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d92998 q = 1) (hb : d112238 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d92998, d112238, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d92998, d112238, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro17651 (p : Pattern) (ha : d93004 p = 1) (hb : d112244 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d92950 q = 1) (hb : d112196 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d92950, d112196, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17638 q ha hb
    | true =>
      simp only [d92950, d112196, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro243 q hb ha
  have h2 (q : Pattern) (ha : d92951 q = 1) (hb : d112197 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d92951, d112197, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92951, d112197, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d92952 q = 1) (hb : d112198 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d92952, d112198, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d92952, d112198, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d92953 q = 1) (hb : d112199 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d92953, d112199, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92953, d112199, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d92957 q = 1) (hb : d112203 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d92957, d112203, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17639 q ha hb
    | true =>
      simp only [d92957, d112203, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro245 q hb ha
  have h6 (q : Pattern) (ha : d92958 q = 1) (hb : d112204 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d92958, d112204, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92958, d112204, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d92959 q = 1) (hb : d112205 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d92959, d112205, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d92959, d112205, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d92973 q = 1) (hb : d112214 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d92973, d112214, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17642 q ha hb
    | true =>
      simp only [d92973, d112214, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17643 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d92930 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d92974 q = 1) (hb : d112215 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d92974, d112215, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d92974, d112215, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
  have h11 (q : Pattern) (ha : d92979 q = 1) (hb : d112220 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d92979, d112220, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17644 q ha hb
    | true =>
      simp only [d92979, d112220, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d92980 q = 1) (hb : d112221 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d92980, d112221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d92980, d112221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d92981 q = 1) (hb : d112222 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d92981, d112222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d92981, d112222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d92982 q = 1) (hb : d112223 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d92982, d112223, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d92982, d112223, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d92983 q = 1) (hb : d112224 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d92983, d112224, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d92983, d112224, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d92986 q = 1) (hb : d112227 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d92986, d112227, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17646 q ha hb
    | true =>
      simp only [d92986, d112227, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro249 q hb ha
  have h17 (q : Pattern) (ha : d92987 q = 1) (hb : d112228 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d92987, d112228, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92987, d112228, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d92988 q = 1) (hb : d112229 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d92988, d112229, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d92988, d112229, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h19 (q : Pattern) (ha : d92989 q = 1) (hb : d112230 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d92989, d112230, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92989, d112230, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d92991 q = 1) (hb : d112232 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d92991, d112232, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17647 q ha hb
    | true =>
      simp only [d92991, d112232, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro251 q hb ha
  have h21 (q : Pattern) (ha : d92992 q = 1) (hb : d112233 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d92992, d112233, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92992, d112233, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
  have h22 (q : Pattern) (ha : d92993 q = 1) (hb : d112234 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d92993, d112234, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d92993, d112234, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h23 (q : Pattern) (ha : d92996 q = 1) (hb : d112236 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d92996, d112236, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17648 q ha hb
    | true =>
      simp only [d92996, d112236, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17649 q ha hb
  have h24 (q : Pattern) (ha : d0 q = 1) (hb : d92939 q = 1) : d0 q = 1 := by
    exact ha
  have h25 (q : Pattern) (ha : d92997 q = 1) (hb : d112237 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d92997, d112237, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
    | true =>
      simp only [d92997, d112237, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q hb ha
  have h26 (q : Pattern) (ha : d92999 q = 1) (hb : d112239 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d92999, d112239, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17650 q ha hb
    | true =>
      simp only [d92999, d112239, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h27 (q : Pattern) (ha : d93000 q = 1) (hb : d112240 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d93000, d112240, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h26 q ha hb
    | true =>
      simp only [d93000, d112240, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h28 (q : Pattern) (ha : d93001 q = 1) (hb : d112241 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d93001, d112241, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q ha hb
    | true =>
      simp only [d93001, d112241, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h27 q ha hb
  have h29 (q : Pattern) (ha : d93002 q = 1) (hb : d112242 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d93002, d112242, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
    | true =>
      simp only [d93002, d112242, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h28 q ha hb
  have h30 (q : Pattern) (ha : d93003 q = 1) (hb : d112243 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d93003, d112243, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d93003, d112243, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h29 q ha hb
  have h31 (q : Pattern) (ha : d93004 q = 1) (hb : d112244 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d93004, d112244, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d93004, d112244, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h30 q ha hb
  exact h31 p ha hb
theorem andIntro17652 (p : Pattern) (ha : d93011 p = 1) (hb : d112246 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d93006 q = 1) (hb : d112176 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d93006, d112176, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17643 q ha hb
    | true =>
      simp only [d93006, d112176, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro217 q hb ha
  have h2 (q : Pattern) (ha : d93007 q = 1) (hb : d112177 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d93007, d112177, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d93007, d112177, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d93008 q = 1) (hb : d112178 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d93008, d112178, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d93008, d112178, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d93009 q = 1) (hb : d112179 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d93009, d112179, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d93009, d112179, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d93010 q = 1) (hb : d112180 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d93010, d112180, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d93010, d112180, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d1827 q = 1) (hb : d53153 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d1827, d53153, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro217 q ha hb
    | true =>
      simp only [d1827, d53153, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d1828 q = 1) (hb : d53154 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d1828, d53154, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1828, d53154, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d1829 q = 1) (hb : d53155 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d1829, d53155, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d1829, d53155, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d1830 q = 1) (hb : d53156 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d1830, d53156, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1830, d53156, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d1831 q = 1) (hb : d53157 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d1831, d53157, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1831, d53157, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d93011 q = 1) (hb : d112246 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d93011, d112246, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d93011, d112246, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
  exact h11 p ha hb
theorem andIntro17653 (p : Pattern) (ha : d93018 p = 1) (hb : d112253 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d92996 q = 1) (hb : d112236 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d92996, d112236, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17648 q ha hb
    | true =>
      simp only [d92996, d112236, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17649 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d92939 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d92997 q = 1) (hb : d112237 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d92997, d112237, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d92997, d112237, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d92999 q = 1) (hb : d112239 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d92999, d112239, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17650 q ha hb
    | true =>
      simp only [d92999, d112239, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d93000 q = 1) (hb : d112240 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d93000, d112240, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d93000, d112240, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d93001 q = 1) (hb : d112241 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d93001, d112241, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d93001, d112241, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d93016 q = 1) (hb : d112251 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d93016, d112251, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d93016, d112251, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d93017 q = 1) (hb : d112252 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d93017, d112252, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d93017, d112252, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d93018 q = 1) (hb : d112253 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d93018, d112253, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d93018, d112253, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro17654 (p : Pattern) (ha : d81870 p = 1) (hb : d99061 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1879 q = 1) (hb : d53205 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d1879, d53205, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro236 q ha hb
    | true =>
      simp only [d1879, d53205, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro225 q ha hb
  have h2 (q : Pattern) (ha : d1880 q = 1) (hb : d53206 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d1880, d53206, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1880, d53206, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d1881 q = 1) (hb : d53207 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d1881, d53207, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1881, d53207, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d7080 q = 1) (hb : d81868 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d7080, d81868, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d7080, d81868, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d76234 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d81869 q = 1) (hb : d99060 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d81869, d99060, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d81869, d99060, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d81870 q = 1) (hb : d99061 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d81870, d99061, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d81870, d99061, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h7 p ha hb
theorem andIntro17655 (p : Pattern) (ha : d93026 p = 1) (hb : d112260 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1874 q = 1) (hb : d53200 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d1874, d53200, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro235 q ha hb
    | true =>
      simp only [d1874, d53200, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro236 q ha hb
  have h2 (q : Pattern) (ha : d1875 q = 1) (hb : d53201 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d1875, d53201, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1875, d53201, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d1876 q = 1) (hb : d53202 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d1876, d53202, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1876, d53202, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d9024 q = 1) (hb : d93024 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d9024, d93024, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d9024, d93024, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d81868 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d93025 q = 1) (hb : d112259 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d93025, d112259, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d93025, d112259, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d93026 q = 1) (hb : d112260 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d93026, d112260, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d93026, d112260, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h7 p ha hb
theorem andIntro17656 (p : Pattern) (ha : d93032 p = 1) (hb : d112266 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d93027 q = 1) (hb : d112261 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d93027, d112261, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17655 q ha hb
    | true =>
      simp only [d93027, d112261, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d93028 q = 1) (hb : d112262 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d93028, d112262, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d93028, d112262, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d81871 q = 1) (hb : d99062 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d81871, d99062, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17654 q ha hb
    | true =>
      simp only [d81871, d99062, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d81872 q = 1) (hb : d99063 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d81872, d99063, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d81872, d99063, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d93029 q = 1) (hb : d112263 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d93029, d112263, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d93029, d112263, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d93030 q = 1) (hb : d112264 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d93030, d112264, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d93030, d112264, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d93031 q = 1) (hb : d112265 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d93031, d112265, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d93031, d112265, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d93032 q = 1) (hb : d112266 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d93032, d112266, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d93032, d112266, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro17657 (p : Pattern) (ha : d93036 p = 1) (hb : d112270 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d81871 q = 1) (hb : d99062 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d81871, d99062, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17654 q ha hb
    | true =>
      simp only [d81871, d99062, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d81872 q = 1) (hb : d99063 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d81872, d99063, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d81872, d99063, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d1908 q = 1) (hb : d53234 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d1908, d53234, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro227 q ha hb
    | true =>
      simp only [d1908, d53234, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d1909 q = 1) (hb : d53235 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d1909, d53235, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1909, d53235, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d93033 q = 1) (hb : d112267 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d93033, d112267, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d93033, d112267, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d93034 q = 1) (hb : d112268 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d93034, d112268, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d93034, d112268, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d93035 q = 1) (hb : d112269 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d93035, d112269, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d93035, d112269, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d93036 q = 1) (hb : d112270 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d93036, d112270, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d93036, d112270, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro17658 (p : Pattern) (ha : d93039 p = 1) (hb : d99061 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1879 q = 1) (hb : d53205 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d1879, d53205, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro236 q ha hb
    | true =>
      simp only [d1879, d53205, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro225 q ha hb
  have h2 (q : Pattern) (ha : d1880 q = 1) (hb : d53206 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d1880, d53206, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1880, d53206, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d1881 q = 1) (hb : d53207 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d1881, d53207, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1881, d53207, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d7080 q = 1) (hb : d81868 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d7080, d81868, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d7080, d81868, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d53223 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d93038 q = 1) (hb : d99060 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d93038, d99060, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d93038, d99060, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d93039 q = 1) (hb : d99061 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d93039, d99061, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d93039, d99061, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h7 p ha hb
theorem andIntro17659 (p : Pattern) (ha : d93051 p = 1) (hb : d112276 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d93040 q = 1) (hb : d99062 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d93040, d99062, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17658 q ha hb
    | true =>
      simp only [d93040, d99062, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d93041 q = 1) (hb : d99063 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d93041, d99063, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d93041, d99063, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d93048 q = 1) (hb : d112273 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d93048, d112273, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d93048, d112273, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d93049 q = 1) (hb : d112274 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d93049, d112274, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d93049, d112274, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d93050 q = 1) (hb : d112275 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d93050, d112275, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d93050, d112275, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d93051 q = 1) (hb : d112276 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d93051, d112276, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d93051, d112276, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro17660 (p : Pattern) (ha : d93057 p = 1) (hb : d112282 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d93037 q = 1) (hb : d112271 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d93037, d112271, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17656 q ha hb
    | true =>
      simp only [d93037, d112271, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17657 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d93046 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d93047 q = 1) (hb : d112272 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d93047, d112272, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d93047, d112272, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d93052 q = 1) (hb : d112277 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d93052, d112277, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17659 q ha hb
    | true =>
      simp only [d93052, d112277, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d93053 q = 1) (hb : d112278 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d93053, d112278, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d93053, d112278, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d93054 q = 1) (hb : d112279 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d93054, d112279, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d93054, d112279, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d93055 q = 1) (hb : d112280 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d93055, d112280, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d93055, d112280, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d93056 q = 1) (hb : d112281 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d93056, d112281, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d93056, d112281, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d93057 q = 1) (hb : d112282 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d93057, d112282, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d93057, d112282, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro17661 (p : Pattern) (ha : d93063 p = 1) (hb : d112288 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d92936 q = 1) (hb : d112182 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d92936, d112182, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92936, d112182, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17635 q ha hb
  have h2 (q : Pattern) (ha : d92937 q = 1) (hb : d112183 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d92937, d112183, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d92937, d112183, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d92945 q = 1) (hb : d112191 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d92945, d112191, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17635 q ha hb
    | true =>
      simp only [d92945, d112191, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17637 q ha hb
  have h4 (q : Pattern) (ha : d92946 q = 1) (hb : d112192 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d92946, d112192, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d92946, d112192, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d92947 q = 1) (hb : d112193 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d92947, d112193, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d92947, d112193, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d93005 q = 1) (hb : d112245 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d93005, d112245, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17645 q ha hb
    | true =>
      simp only [d93005, d112245, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17651 q ha hb
  have h7 (q : Pattern) (ha : d93012 q = 1) (hb : d112247 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d93012, d112247, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17652 q ha hb
    | true =>
      simp only [d93012, d112247, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro223 q hb ha
  have h8 (q : Pattern) (ha : d93013 q = 1) (hb : d112248 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d93013, d112248, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d93013, d112248, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d93014 q = 1) (hb : d112249 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d93014, d112249, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d93014, d112249, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h10 (q : Pattern) (ha : d93015 q = 1) (hb : d112250 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d93015, d112250, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d93015, d112250, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d93019 q = 1) (hb : d112254 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d93019, d112254, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d93019, d112254, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17653 q ha hb
  have h12 (q : Pattern) (ha : d1848 q = 1) (hb : d53174 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d1848, d53174, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1848, d53174, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro224 q ha hb
  have h13 (q : Pattern) (ha : d93020 q = 1) (hb : d112255 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d93020, d112255, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d93020, d112255, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
  have h14 (q : Pattern) (ha : d93021 q = 1) (hb : d112256 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d93021, d112256, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d93021, d112256, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h15 (q : Pattern) (ha : d93022 q = 1) (hb : d112257 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d93022, d112257, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d93022, d112257, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h16 (q : Pattern) (ha : d93023 q = 1) (hb : d112258 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d93023, d112258, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d93023, d112258, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d93058 q = 1) (hb : d112283 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d93058, d112283, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d93058, d112283, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17660 q ha hb
  have h18 (q : Pattern) (ha : d1981 q = 1) (hb : d53260 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d1981, d53260, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1981, d53260, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro229 q ha hb
  have h19 (q : Pattern) (ha : d93059 q = 1) (hb : d112284 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d93059, d112284, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d93059, d112284, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q hb ha
  have h20 (q : Pattern) (ha : d93060 q = 1) (hb : d112285 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d93060, d112285, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d93060, d112285, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h21 (q : Pattern) (ha : d93061 q = 1) (hb : d112286 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d93061, d112286, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d93061, d112286, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h22 (q : Pattern) (ha : d93062 q = 1) (hb : d112287 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d93062, d112287, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d93062, d112287, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h23 (q : Pattern) (ha : d93063 q = 1) (hb : d112288 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d93063, d112288, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d93063, d112288, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
  exact h23 p ha hb
theorem andIntro17662 (p : Pattern) (ha : d93069 p = 1) (hb : d112294 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d93064 q = 1) (hb : d112289 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d93064, d112289, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d93064, d112289, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17661 q ha hb
  have h2 (q : Pattern) (ha : d93065 q = 1) (hb : d112290 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d93065, d112290, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d93065, d112290, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d93066 q = 1) (hb : d112291 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d93066, d112291, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d93066, d112291, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d93067 q = 1) (hb : d112292 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d93067, d112292, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d93067, d112292, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d93068 q = 1) (hb : d112293 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d93068, d112293, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d93068, d112293, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d93069 q = 1) (hb : d112294 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d93069, d112294, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d93069, d112294, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro17663 (p : Pattern) (ha : d93075 p = 1) (hb : d99091 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d2073 q = 1) (hb : d53352 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d2073, d53352, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro269 q ha hb
    | true =>
      simp only [d2073, d53352, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro270 q ha hb
  have h2 (q : Pattern) (ha : d2074 q = 1) (hb : d53353 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d2074, d53353, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2074, d53353, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d2075 q = 1) (hb : d53354 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d2075, d53354, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2075, d53354, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d7115 q = 1) (hb : d81903 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d7115, d81903, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d7115, d81903, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d53369 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d93074 q = 1) (hb : d99090 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d93074, d99090, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d93074, d99090, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d93075 q = 1) (hb : d99091 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d93075, d99091, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d93075, d99091, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h7 p ha hb
theorem andIntro17664 (p : Pattern) (ha : d93081 p = 1) (hb : d112302 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d93076 q = 1) (hb : d99092 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d93076, d99092, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17663 q ha hb
    | true =>
      simp only [d93076, d99092, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d93077 q = 1) (hb : d99093 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d93077, d99093, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d93077, d99093, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d2097 q = 1) (hb : d53376 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d2097, d53376, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro274 q ha hb
    | true =>
      simp only [d2097, d53376, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d2098 q = 1) (hb : d53377 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d2098, d53377, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2098, d53377, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d93078 q = 1) (hb : d112299 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d93078, d112299, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d93078, d112299, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d93079 q = 1) (hb : d112300 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d93079, d112300, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d93079, d112300, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d93080 q = 1) (hb : d112301 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d93080, d112301, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d93080, d112301, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d93081 q = 1) (hb : d112302 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d93081, d112302, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d93081, d112302, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro17665 (p : Pattern) (ha : d93087 p = 1) (hb : d112308 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d93082 q = 1) (hb : d112303 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d93082, d112303, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17664 q ha hb
    | true =>
      simp only [d93082, d112303, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro276 q hb ha
  have h2 (q : Pattern) (ha : d93083 q = 1) (hb : d112304 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d93083, d112304, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d93083, d112304, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d93084 q = 1) (hb : d112305 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d93084, d112305, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d93084, d112305, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d93085 q = 1) (hb : d112306 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d93085, d112306, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d93085, d112306, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d93086 q = 1) (hb : d112307 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d93086, d112307, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d93086, d112307, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d93087 q = 1) (hb : d112308 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d93087, d112308, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d93087, d112308, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro17666 (p : Pattern) (ha : d93090 p = 1) (hb : d112311 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d93076 q = 1) (hb : d99092 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d93076, d99092, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17663 q ha hb
    | true =>
      simp only [d93076, d99092, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d93077 q = 1) (hb : d99093 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d93077, d99093, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d93077, d99093, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d2097 q = 1) (hb : d53376 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d2097, d53376, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro274 q ha hb
    | true =>
      simp only [d2097, d53376, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d2098 q = 1) (hb : d53377 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d2098, d53377, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2098, d53377, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d93078 q = 1) (hb : d112299 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d93078, d112299, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d93078, d112299, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d93079 q = 1) (hb : d112300 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d93079, d112300, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d93079, d112300, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d93080 q = 1) (hb : d112301 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d93080, d112301, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d93080, d112301, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d93090 q = 1) (hb : d112311 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d93090, d112311, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d93090, d112311, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro17667 (p : Pattern) (ha : d93096 p = 1) (hb : d112317 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d93082 q = 1) (hb : d112303 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d93082, d112303, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17664 q ha hb
    | true =>
      simp only [d93082, d112303, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro276 q hb ha
  have h2 (q : Pattern) (ha : d93083 q = 1) (hb : d112304 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d93083, d112304, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d93083, d112304, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d93084 q = 1) (hb : d112305 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d93084, d112305, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d93084, d112305, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d93085 q = 1) (hb : d112306 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d93085, d112306, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d93085, d112306, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d93086 q = 1) (hb : d112307 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d93086, d112307, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d93086, d112307, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d93091 q = 1) (hb : d112312 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d93091, d112312, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17666 q ha hb
    | true =>
      simp only [d93091, d112312, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro279 q hb ha
  have h7 (q : Pattern) (ha : d93092 q = 1) (hb : d112313 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d93092, d112313, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d93092, d112313, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d93093 q = 1) (hb : d112314 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d93093, d112314, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d93093, d112314, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d93094 q = 1) (hb : d112315 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d93094, d112315, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d93094, d112315, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d93095 q = 1) (hb : d112316 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d93095, d112316, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d93095, d112316, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d93096 q = 1) (hb : d112317 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d93096, d112317, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d93096, d112317, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro17668 (p : Pattern) (ha : d93101 p = 1) (hb : d112322 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d93076 q = 1) (hb : d99092 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d93076, d99092, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17663 q ha hb
    | true =>
      simp only [d93076, d99092, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d93077 q = 1) (hb : d99093 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d93077, d99093, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d93077, d99093, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d2097 q = 1) (hb : d53376 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d2097, d53376, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro274 q ha hb
    | true =>
      simp only [d2097, d53376, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d2098 q = 1) (hb : d53377 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d2098, d53377, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2098, d53377, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d93078 q = 1) (hb : d112299 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d93078, d112299, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d93078, d112299, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d93079 q = 1) (hb : d112300 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d93079, d112300, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d93079, d112300, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d93100 q = 1) (hb : d112321 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d93100, d112321, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d93100, d112321, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d93101 q = 1) (hb : d112322 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d93101, d112322, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d93101, d112322, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro17669 (p : Pattern) (ha : d93108 p = 1) (hb : d112329 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d93076 q = 1) (hb : d99092 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d93076, d99092, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17663 q ha hb
    | true =>
      simp only [d93076, d99092, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d93077 q = 1) (hb : d99093 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d93077, d99093, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d93077, d99093, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d2097 q = 1) (hb : d53376 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d2097, d53376, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro274 q ha hb
    | true =>
      simp only [d2097, d53376, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d2098 q = 1) (hb : d53377 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d2098, d53377, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2098, d53377, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d93078 q = 1) (hb : d112299 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d93078, d112299, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d93078, d112299, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d93106 q = 1) (hb : d112327 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d93106, d112327, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d93106, d112327, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d93107 q = 1) (hb : d112328 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d93107, d112328, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d93107, d112328, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d93108 q = 1) (hb : d112329 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d93108, d112329, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d93108, d112329, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro17670 (p : Pattern) (ha : d81905 p = 1) (hb : d99091 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d2073 q = 1) (hb : d53352 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d2073, d53352, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro269 q ha hb
    | true =>
      simp only [d2073, d53352, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro270 q ha hb
  have h2 (q : Pattern) (ha : d2074 q = 1) (hb : d53353 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d2074, d53353, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2074, d53353, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d2075 q = 1) (hb : d53354 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d2075, d53354, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2075, d53354, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d7115 q = 1) (hb : d81903 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d7115, d81903, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d7115, d81903, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d69340 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d81904 q = 1) (hb : d99090 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d81904, d99090, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d81904, d99090, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d81905 q = 1) (hb : d99091 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d81905, d99091, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d81905, d99091, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h7 p ha hb
theorem andIntro17671 (p : Pattern) (ha : d93114 p = 1) (hb : d112334 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d2150 q = 1) (hb : d53429 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d2150, d53429, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro290 q ha hb
    | true =>
      simp only [d2150, d53429, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro269 q ha hb
  have h2 (q : Pattern) (ha : d2151 q = 1) (hb : d53430 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d2151, d53430, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2151, d53430, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d2152 q = 1) (hb : d53431 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d2152, d53431, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2152, d53431, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d9117 q = 1) (hb : d93112 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d9117, d93112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d9117, d93112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d81903 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d93113 q = 1) (hb : d112333 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d93113, d112333, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d93113, d112333, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d93114 q = 1) (hb : d112334 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d93114, d112334, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d93114, d112334, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h7 p ha hb
theorem andIntro17672 (p : Pattern) (ha : d93120 p = 1) (hb : d112340 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d93115 q = 1) (hb : d112335 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d93115, d112335, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17671 q ha hb
    | true =>
      simp only [d93115, d112335, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d93116 q = 1) (hb : d112336 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d93116, d112336, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d93116, d112336, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d81906 q = 1) (hb : d99092 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d81906, d99092, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17670 q ha hb
    | true =>
      simp only [d81906, d99092, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d81907 q = 1) (hb : d99093 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d81907, d99093, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d81907, d99093, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d93117 q = 1) (hb : d112337 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d93117, d112337, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d93117, d112337, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d93118 q = 1) (hb : d112338 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d93118, d112338, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d93118, d112338, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d93119 q = 1) (hb : d112339 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d93119, d112339, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d93119, d112339, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d93120 q = 1) (hb : d112340 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d93120, d112340, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d93120, d112340, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro17673 (p : Pattern) (ha : d93124 p = 1) (hb : d112302 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d81906 q = 1) (hb : d99092 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d81906, d99092, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17670 q ha hb
    | true =>
      simp only [d81906, d99092, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d81907 q = 1) (hb : d99093 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d81907, d99093, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d81907, d99093, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d2097 q = 1) (hb : d53376 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d2097, d53376, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro274 q ha hb
    | true =>
      simp only [d2097, d53376, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d2098 q = 1) (hb : d53377 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d2098, d53377, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2098, d53377, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d93121 q = 1) (hb : d112299 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d93121, d112299, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d93121, d112299, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d93122 q = 1) (hb : d112300 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d93122, d112300, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d93122, d112300, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d93123 q = 1) (hb : d112301 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d93123, d112301, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d93123, d112301, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d93124 q = 1) (hb : d112302 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d93124, d112302, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d93124, d112302, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro17674 (p : Pattern) (ha : d93130 p = 1) (hb : d112346 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d93076 q = 1) (hb : d99092 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d93076, d99092, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17663 q ha hb
    | true =>
      simp only [d93076, d99092, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d93077 q = 1) (hb : d99093 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d93077, d99093, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d93077, d99093, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d93127 q = 1) (hb : d112343 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d93127, d112343, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d93127, d112343, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d93128 q = 1) (hb : d112344 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d93128, d112344, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d93128, d112344, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d93129 q = 1) (hb : d112345 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d93129, d112345, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d93129, d112345, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d93130 q = 1) (hb : d112346 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d93130, d112346, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d93130, d112346, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro17675 (p : Pattern) (ha : d93136 p = 1) (hb : d112352 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d93102 q = 1) (hb : d112323 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d93102, d112323, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17668 q ha hb
    | true =>
      simp only [d93102, d112323, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro302 q hb ha
  have h2 (q : Pattern) (ha : d93103 q = 1) (hb : d112324 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d93103, d112324, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d93103, d112324, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d93104 q = 1) (hb : d112325 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d93104, d112325, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d93104, d112325, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d93105 q = 1) (hb : d112326 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d93105, d112326, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d93105, d112326, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d93109 q = 1) (hb : d112330 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d93109, d112330, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17669 q ha hb
    | true =>
      simp only [d93109, d112330, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro304 q hb ha
  have h6 (q : Pattern) (ha : d93110 q = 1) (hb : d112331 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d93110, d112331, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d93110, d112331, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d93111 q = 1) (hb : d112332 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d93111, d112332, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d93111, d112332, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d93125 q = 1) (hb : d112341 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d93125, d112341, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17672 q ha hb
    | true =>
      simp only [d93125, d112341, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17673 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d93082 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d93126 q = 1) (hb : d112342 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d93126, d112342, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d93126, d112342, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
  have h11 (q : Pattern) (ha : d93131 q = 1) (hb : d112347 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d93131, d112347, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17674 q ha hb
    | true =>
      simp only [d93131, d112347, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d93132 q = 1) (hb : d112348 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d93132, d112348, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d93132, d112348, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d93133 q = 1) (hb : d112349 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d93133, d112349, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d93133, d112349, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d93134 q = 1) (hb : d112350 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d93134, d112350, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d93134, d112350, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d93135 q = 1) (hb : d112351 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d93135, d112351, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d93135, d112351, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d93136 q = 1) (hb : d112352 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d93136, d112352, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d93136, d112352, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  exact h16 p ha hb
theorem andIntro17676 (p : Pattern) (ha : d93137 p = 1) (hb : d112353 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d93076 q = 1) (hb : d99092 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d93076, d99092, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17663 q ha hb
    | true =>
      simp only [d93076, d99092, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d93077 q = 1) (hb : d99093 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d93077, d99093, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d93077, d99093, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d2097 q = 1) (hb : d53376 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d2097, d53376, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro274 q ha hb
    | true =>
      simp only [d2097, d53376, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d2098 q = 1) (hb : d53377 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d2098, d53377, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2098, d53377, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d93078 q = 1) (hb : d112299 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d93078, d112299, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d93078, d112299, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d93079 q = 1) (hb : d112300 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d93079, d112300, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d93079, d112300, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d93100 q = 1) (hb : d112321 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d93100, d112321, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d93100, d112321, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d93137 q = 1) (hb : d112353 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d93137, d112353, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d93137, d112353, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro17677 (p : Pattern) (ha : d93142 p = 1) (hb : d112358 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d93076 q = 1) (hb : d99092 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d93076, d99092, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17663 q ha hb
    | true =>
      simp only [d93076, d99092, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d93077 q = 1) (hb : d99093 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d93077, d99093, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d93077, d99093, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d2097 q = 1) (hb : d53376 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d2097, d53376, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro274 q ha hb
    | true =>
      simp only [d2097, d53376, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d2098 q = 1) (hb : d53377 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d2098, d53377, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2098, d53377, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d93078 q = 1) (hb : d112299 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d93078, d112299, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d93078, d112299, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d93106 q = 1) (hb : d112327 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d93106, d112327, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d93106, d112327, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d93107 q = 1) (hb : d112328 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d93107, d112328, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d93107, d112328, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d93142 q = 1) (hb : d112358 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d93142, d112358, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d93142, d112358, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro17678 (p : Pattern) (ha : d93146 p = 1) (hb : d112362 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d93115 q = 1) (hb : d112335 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d93115, d112335, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17671 q ha hb
    | true =>
      simp only [d93115, d112335, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d93116 q = 1) (hb : d112336 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d93116, d112336, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d93116, d112336, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d81906 q = 1) (hb : d99092 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d81906, d99092, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17670 q ha hb
    | true =>
      simp only [d81906, d99092, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d81907 q = 1) (hb : d99093 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d81907, d99093, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d81907, d99093, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d93117 q = 1) (hb : d112337 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d93117, d112337, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d93117, d112337, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d93118 q = 1) (hb : d112338 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d93118, d112338, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d93118, d112338, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d93119 q = 1) (hb : d112339 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d93119, d112339, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d93119, d112339, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d93146 q = 1) (hb : d112362 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d93146, d112362, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d93146, d112362, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro17679 (p : Pattern) (ha : d93147 p = 1) (hb : d112311 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d81906 q = 1) (hb : d99092 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d81906, d99092, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17670 q ha hb
    | true =>
      simp only [d81906, d99092, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d81907 q = 1) (hb : d99093 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d81907, d99093, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d81907, d99093, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d2097 q = 1) (hb : d53376 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d2097, d53376, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro274 q ha hb
    | true =>
      simp only [d2097, d53376, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d2098 q = 1) (hb : d53377 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d2098, d53377, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2098, d53377, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d93121 q = 1) (hb : d112299 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d93121, d112299, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d93121, d112299, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d93122 q = 1) (hb : d112300 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d93122, d112300, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d93122, d112300, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d93123 q = 1) (hb : d112301 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d93123, d112301, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d93123, d112301, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d93147 q = 1) (hb : d112311 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d93147, d112311, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d93147, d112311, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro17680 (p : Pattern) (ha : d93150 p = 1) (hb : d112365 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d93076 q = 1) (hb : d99092 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d93076, d99092, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17663 q ha hb
    | true =>
      simp only [d93076, d99092, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d93077 q = 1) (hb : d99093 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d93077, d99093, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d93077, d99093, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d93127 q = 1) (hb : d112343 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d93127, d112343, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d93127, d112343, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d93128 q = 1) (hb : d112344 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d93128, d112344, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d93128, d112344, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d93129 q = 1) (hb : d112345 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d93129, d112345, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d93129, d112345, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d93150 q = 1) (hb : d112365 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d93150, d112365, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d93150, d112365, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro17681 (p : Pattern) (ha : d93156 p = 1) (hb : d112371 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d93102 q = 1) (hb : d112323 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d93102, d112323, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17668 q ha hb
    | true =>
      simp only [d93102, d112323, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro302 q hb ha
  have h2 (q : Pattern) (ha : d93103 q = 1) (hb : d112324 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d93103, d112324, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d93103, d112324, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d93104 q = 1) (hb : d112325 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d93104, d112325, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d93104, d112325, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d93105 q = 1) (hb : d112326 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d93105, d112326, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d93105, d112326, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d93109 q = 1) (hb : d112330 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d93109, d112330, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17669 q ha hb
    | true =>
      simp only [d93109, d112330, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro304 q hb ha
  have h6 (q : Pattern) (ha : d93110 q = 1) (hb : d112331 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d93110, d112331, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d93110, d112331, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d93111 q = 1) (hb : d112332 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d93111, d112332, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d93111, d112332, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d93125 q = 1) (hb : d112341 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d93125, d112341, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17672 q ha hb
    | true =>
      simp only [d93125, d112341, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17673 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d93082 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d93126 q = 1) (hb : d112342 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d93126, d112342, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d93126, d112342, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
  have h11 (q : Pattern) (ha : d93131 q = 1) (hb : d112347 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d93131, d112347, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17674 q ha hb
    | true =>
      simp only [d93131, d112347, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d93132 q = 1) (hb : d112348 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d93132, d112348, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d93132, d112348, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d93133 q = 1) (hb : d112349 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d93133, d112349, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d93133, d112349, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d93134 q = 1) (hb : d112350 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d93134, d112350, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d93134, d112350, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d93135 q = 1) (hb : d112351 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d93135, d112351, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d93135, d112351, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d93138 q = 1) (hb : d112354 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d93138, d112354, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17676 q ha hb
    | true =>
      simp only [d93138, d112354, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro308 q hb ha
  have h17 (q : Pattern) (ha : d93139 q = 1) (hb : d112355 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d93139, d112355, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d93139, d112355, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d93140 q = 1) (hb : d112356 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d93140, d112356, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d93140, d112356, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h19 (q : Pattern) (ha : d93141 q = 1) (hb : d112357 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d93141, d112357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d93141, d112357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d93143 q = 1) (hb : d112359 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d93143, d112359, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17677 q ha hb
    | true =>
      simp only [d93143, d112359, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro310 q hb ha
  have h21 (q : Pattern) (ha : d93144 q = 1) (hb : d112360 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d93144, d112360, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d93144, d112360, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
  have h22 (q : Pattern) (ha : d93145 q = 1) (hb : d112361 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d93145, d112361, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d93145, d112361, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h23 (q : Pattern) (ha : d93148 q = 1) (hb : d112363 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d93148, d112363, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17678 q ha hb
    | true =>
      simp only [d93148, d112363, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17679 q ha hb
  have h24 (q : Pattern) (ha : d0 q = 1) (hb : d93091 q = 1) : d0 q = 1 := by
    exact ha
  have h25 (q : Pattern) (ha : d93149 q = 1) (hb : d112364 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d93149, d112364, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
    | true =>
      simp only [d93149, d112364, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q hb ha
  have h26 (q : Pattern) (ha : d93151 q = 1) (hb : d112366 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d93151, d112366, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17680 q ha hb
    | true =>
      simp only [d93151, d112366, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h27 (q : Pattern) (ha : d93152 q = 1) (hb : d112367 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d93152, d112367, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h26 q ha hb
    | true =>
      simp only [d93152, d112367, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h28 (q : Pattern) (ha : d93153 q = 1) (hb : d112368 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d93153, d112368, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q ha hb
    | true =>
      simp only [d93153, d112368, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h27 q ha hb
  have h29 (q : Pattern) (ha : d93154 q = 1) (hb : d112369 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d93154, d112369, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
    | true =>
      simp only [d93154, d112369, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h28 q ha hb
  have h30 (q : Pattern) (ha : d93155 q = 1) (hb : d112370 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d93155, d112370, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d93155, d112370, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h29 q ha hb
  have h31 (q : Pattern) (ha : d93156 q = 1) (hb : d112371 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d93156, d112371, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d93156, d112371, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h30 q ha hb
  exact h31 p ha hb
theorem andIntro17682 (p : Pattern) (ha : d93163 p = 1) (hb : d112373 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d93158 q = 1) (hb : d112303 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d93158, d112303, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17673 q ha hb
    | true =>
      simp only [d93158, d112303, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro276 q hb ha
  have h2 (q : Pattern) (ha : d93159 q = 1) (hb : d112304 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d93159, d112304, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d93159, d112304, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d93160 q = 1) (hb : d112305 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d93160, d112305, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d93160, d112305, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d93161 q = 1) (hb : d112306 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d93161, d112306, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d93161, d112306, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d93162 q = 1) (hb : d112307 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d93162, d112307, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d93162, d112307, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d2305 q = 1) (hb : d53470 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d2305, d53470, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro276 q ha hb
    | true =>
      simp only [d2305, d53470, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d2306 q = 1) (hb : d53471 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d2306, d53471, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2306, d53471, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d2307 q = 1) (hb : d53472 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d2307, d53472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d2307, d53472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d2308 q = 1) (hb : d53473 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d2308, d53473, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2308, d53473, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d2309 q = 1) (hb : d53474 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d2309, d53474, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2309, d53474, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d93163 q = 1) (hb : d112373 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d93163, d112373, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d93163, d112373, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
  exact h11 p ha hb
theorem andIntro17683 (p : Pattern) (ha : d93170 p = 1) (hb : d112380 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d93148 q = 1) (hb : d112363 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d93148, d112363, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17678 q ha hb
    | true =>
      simp only [d93148, d112363, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17679 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d93091 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d93149 q = 1) (hb : d112364 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d93149, d112364, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d93149, d112364, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d93151 q = 1) (hb : d112366 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d93151, d112366, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17680 q ha hb
    | true =>
      simp only [d93151, d112366, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d93152 q = 1) (hb : d112367 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d93152, d112367, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d93152, d112367, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d93153 q = 1) (hb : d112368 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d93153, d112368, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d93153, d112368, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d93168 q = 1) (hb : d112378 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d93168, d112378, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d93168, d112378, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d93169 q = 1) (hb : d112379 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d93169, d112379, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d93169, d112379, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d93170 q = 1) (hb : d112380 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d93170, d112380, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d93170, d112380, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro17684 (p : Pattern) (ha : d81951 p = 1) (hb : d99124 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d2357 q = 1) (hb : d53522 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d2357, d53522, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro295 q ha hb
    | true =>
      simp only [d2357, d53522, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro284 q ha hb
  have h2 (q : Pattern) (ha : d2358 q = 1) (hb : d53523 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d2358, d53523, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2358, d53523, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d2359 q = 1) (hb : d53524 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d2359, d53524, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2359, d53524, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d7161 q = 1) (hb : d81949 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d7161, d81949, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d7161, d81949, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d76370 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d81950 q = 1) (hb : d99123 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d81950, d99123, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d81950, d99123, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d81951 q = 1) (hb : d99124 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d81951, d99124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d81951, d99124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h7 p ha hb
theorem andIntro17685 (p : Pattern) (ha : d93178 p = 1) (hb : d112387 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d2352 q = 1) (hb : d53517 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d2352, d53517, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro294 q ha hb
    | true =>
      simp only [d2352, d53517, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro295 q ha hb
  have h2 (q : Pattern) (ha : d2353 q = 1) (hb : d53518 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d2353, d53518, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2353, d53518, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d2354 q = 1) (hb : d53519 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d2354, d53519, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2354, d53519, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d9193 q = 1) (hb : d93176 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d9193, d93176, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d9193, d93176, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d81949 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d93177 q = 1) (hb : d112386 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d93177, d112386, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d93177, d112386, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d93178 q = 1) (hb : d112387 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d93178, d112387, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d93178, d112387, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h7 p ha hb
theorem andIntro17686 (p : Pattern) (ha : d93184 p = 1) (hb : d112393 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d93179 q = 1) (hb : d112388 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d93179, d112388, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17685 q ha hb
    | true =>
      simp only [d93179, d112388, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d93180 q = 1) (hb : d112389 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d93180, d112389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d93180, d112389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d81952 q = 1) (hb : d99125 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d81952, d99125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17684 q ha hb
    | true =>
      simp only [d81952, d99125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d81953 q = 1) (hb : d99126 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d81953, d99126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d81953, d99126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d93181 q = 1) (hb : d112390 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d93181, d112390, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d93181, d112390, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d93182 q = 1) (hb : d112391 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d93182, d112391, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d93182, d112391, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d93183 q = 1) (hb : d112392 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d93183, d112392, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d93183, d112392, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d93184 q = 1) (hb : d112393 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d93184, d112393, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d93184, d112393, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro17687 (p : Pattern) (ha : d93188 p = 1) (hb : d112397 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d81952 q = 1) (hb : d99125 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d81952, d99125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17684 q ha hb
    | true =>
      simp only [d81952, d99125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d81953 q = 1) (hb : d99126 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d81953, d99126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d81953, d99126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d2386 q = 1) (hb : d53551 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d2386, d53551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro286 q ha hb
    | true =>
      simp only [d2386, d53551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d2387 q = 1) (hb : d53552 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d2387, d53552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2387, d53552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d93185 q = 1) (hb : d112394 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d93185, d112394, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d93185, d112394, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d93186 q = 1) (hb : d112395 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d93186, d112395, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d93186, d112395, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d93187 q = 1) (hb : d112396 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d93187, d112396, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d93187, d112396, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d93188 q = 1) (hb : d112397 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d93188, d112397, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d93188, d112397, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro17688 (p : Pattern) (ha : d93191 p = 1) (hb : d99124 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d2357 q = 1) (hb : d53522 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d2357, d53522, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro295 q ha hb
    | true =>
      simp only [d2357, d53522, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro284 q ha hb
  have h2 (q : Pattern) (ha : d2358 q = 1) (hb : d53523 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d2358, d53523, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2358, d53523, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d2359 q = 1) (hb : d53524 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d2359, d53524, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2359, d53524, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d7161 q = 1) (hb : d81949 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d7161, d81949, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d7161, d81949, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d53540 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d93190 q = 1) (hb : d99123 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d93190, d99123, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d93190, d99123, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d93191 q = 1) (hb : d99124 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d93191, d99124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d93191, d99124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h7 p ha hb
theorem andIntro17689 (p : Pattern) (ha : d93203 p = 1) (hb : d112403 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d93192 q = 1) (hb : d99125 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d93192, d99125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17688 q ha hb
    | true =>
      simp only [d93192, d99125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d93193 q = 1) (hb : d99126 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d93193, d99126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d93193, d99126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d93200 q = 1) (hb : d112400 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d93200, d112400, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d93200, d112400, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d93201 q = 1) (hb : d112401 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d93201, d112401, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d93201, d112401, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d93202 q = 1) (hb : d112402 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d93202, d112402, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d93202, d112402, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d93203 q = 1) (hb : d112403 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d93203, d112403, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d93203, d112403, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro17690 (p : Pattern) (ha : d93209 p = 1) (hb : d112409 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d93189 q = 1) (hb : d112398 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d93189, d112398, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17686 q ha hb
    | true =>
      simp only [d93189, d112398, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17687 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d93198 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d93199 q = 1) (hb : d112399 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d93199, d112399, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d93199, d112399, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d93204 q = 1) (hb : d112404 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d93204, d112404, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17689 q ha hb
    | true =>
      simp only [d93204, d112404, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d93205 q = 1) (hb : d112405 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d93205, d112405, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d93205, d112405, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d93206 q = 1) (hb : d112406 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d93206, d112406, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d93206, d112406, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d93207 q = 1) (hb : d112407 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d93207, d112407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d93207, d112407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d93208 q = 1) (hb : d112408 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d93208, d112408, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d93208, d112408, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d93209 q = 1) (hb : d112409 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d93209, d112409, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d93209, d112409, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro17691 (p : Pattern) (ha : d93215 p = 1) (hb : d112415 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d93088 q = 1) (hb : d112309 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d93088, d112309, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d93088, d112309, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17665 q ha hb
  have h2 (q : Pattern) (ha : d93089 q = 1) (hb : d112310 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d93089, d112310, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d93089, d112310, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d93097 q = 1) (hb : d112318 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d93097, d112318, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17665 q ha hb
    | true =>
      simp only [d93097, d112318, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17667 q ha hb
  have h4 (q : Pattern) (ha : d93098 q = 1) (hb : d112319 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d93098, d112319, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d93098, d112319, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d93099 q = 1) (hb : d112320 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d93099, d112320, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d93099, d112320, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d93157 q = 1) (hb : d112372 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d93157, d112372, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17675 q ha hb
    | true =>
      simp only [d93157, d112372, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17681 q ha hb
  have h7 (q : Pattern) (ha : d93164 q = 1) (hb : d112374 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d93164, d112374, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17682 q ha hb
    | true =>
      simp only [d93164, d112374, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro282 q hb ha
  have h8 (q : Pattern) (ha : d93165 q = 1) (hb : d112375 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d93165, d112375, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d93165, d112375, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d93166 q = 1) (hb : d112376 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d93166, d112376, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d93166, d112376, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h10 (q : Pattern) (ha : d93167 q = 1) (hb : d112377 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d93167, d112377, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d93167, d112377, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d93171 q = 1) (hb : d112381 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d93171, d112381, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d93171, d112381, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17683 q ha hb
  have h12 (q : Pattern) (ha : d2326 q = 1) (hb : d53491 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d2326, d53491, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2326, d53491, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro283 q ha hb
  have h13 (q : Pattern) (ha : d93172 q = 1) (hb : d112382 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d93172, d112382, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d93172, d112382, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
  have h14 (q : Pattern) (ha : d93173 q = 1) (hb : d112383 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d93173, d112383, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d93173, d112383, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h15 (q : Pattern) (ha : d93174 q = 1) (hb : d112384 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d93174, d112384, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d93174, d112384, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h16 (q : Pattern) (ha : d93175 q = 1) (hb : d112385 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d93175, d112385, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d93175, d112385, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d93210 q = 1) (hb : d112410 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d93210, d112410, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d93210, d112410, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17690 q ha hb
  have h18 (q : Pattern) (ha : d2459 q = 1) (hb : d53577 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d2459, d53577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2459, d53577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro288 q ha hb
  have h19 (q : Pattern) (ha : d93211 q = 1) (hb : d112411 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d93211, d112411, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d93211, d112411, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q hb ha
  have h20 (q : Pattern) (ha : d93212 q = 1) (hb : d112412 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d93212, d112412, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d93212, d112412, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h21 (q : Pattern) (ha : d93213 q = 1) (hb : d112413 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d93213, d112413, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d93213, d112413, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h22 (q : Pattern) (ha : d93214 q = 1) (hb : d112414 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d93214, d112414, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d93214, d112414, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h23 (q : Pattern) (ha : d93215 q = 1) (hb : d112415 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d93215, d112415, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d93215, d112415, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
  exact h23 p ha hb
theorem andIntro17692 (p : Pattern) (ha : d93221 p = 1) (hb : d112421 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d93216 q = 1) (hb : d112416 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d93216, d112416, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d93216, d112416, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17691 q ha hb
  have h2 (q : Pattern) (ha : d93217 q = 1) (hb : d112417 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d93217, d112417, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d93217, d112417, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d93218 q = 1) (hb : d112418 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d93218, d112418, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d93218, d112418, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d93219 q = 1) (hb : d112419 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d93219, d112419, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d93219, d112419, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d93220 q = 1) (hb : d112420 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d93220, d112420, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d93220, d112420, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d93221 q = 1) (hb : d112421 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d93221, d112421, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d93221, d112421, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro17693 (p : Pattern) (ha : d93227 p = 1) (hb : d112427 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d92620 q = 1) (hb : d111920 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d92620, d111920, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17544 q ha hb
    | true =>
      simp only [d92620, d111920, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17572 q ha hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d92769 q = 1) (hb : d112044 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d92769, d112044, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d92769, d112044, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17602 q ha hb
  have h3 (q : Pattern) (ha : d92770 q = 1) (hb : d112045 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d92770, d112045, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d92770, d112045, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d92919 q = 1) (hb : d112169 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d92919, d112169, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d92919, d112169, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17632 q ha hb
  have h5 (q : Pattern) (ha : d92920 q = 1) (hb : d112170 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d92920, d112170, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d92920, d112170, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d92921 q = 1) (hb : d112171 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d92921, d112171, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d92921, d112171, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d93070 q = 1) (hb : d112295 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d93070, d112295, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d93070, d112295, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17662 q ha hb
  have h8 (q : Pattern) (ha : d93071 q = 1) (hb : d112296 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d93071, d112296, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d93071, d112296, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d93072 q = 1) (hb : d112297 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d93072, d112297, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d93072, d112297, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d93073 q = 1) (hb : d112298 q = 1) : d0 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d93073, d112298, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d93073, d112298, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d93222 q = 1) (hb : d112422 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d93222, d112422, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d93222, d112422, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17692 q ha hb
  have h12 (q : Pattern) (ha : d93223 q = 1) (hb : d112423 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d93223, d112423, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d93223, d112423, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d93224 q = 1) (hb : d112424 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d93224, d112424, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d93224, d112424, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d93225 q = 1) (hb : d112425 q = 1) : d0 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d93225, d112425, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d93225, d112425, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d93226 q = 1) (hb : d112426 q = 1) : d0 q = 1 := by
    cases bit : q 10250 with
    | false =>
      simp only [d93226, d112426, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d93226, d112426, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d93227 q = 1) (hb : d112427 q = 1) : d0 q = 1 := by
    cases bit : q 260 with
    | false =>
      simp only [d93227, d112427, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d93227, d112427, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  exact h16 p ha hb
theorem andIntro17694 (p : Pattern) (ha : d93233 p = 1) (hb : d112433 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d93228 q = 1) (hb : d112428 q = 1) : d0 q = 1 := by
    cases bit : q 259 with
    | false =>
      simp only [d93228, d112428, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17693 q ha hb
    | true =>
      simp only [d93228, d112428, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d93229 q = 1) (hb : d112429 q = 1) : d0 q = 1 := by
    cases bit : q 258 with
    | false =>
      simp only [d93229, d112429, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d93229, d112429, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d93230 q = 1) (hb : d112430 q = 1) : d0 q = 1 := by
    cases bit : q 257 with
    | false =>
      simp only [d93230, d112430, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d93230, d112430, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d93231 q = 1) (hb : d112431 q = 1) : d0 q = 1 := by
    cases bit : q 256 with
    | false =>
      simp only [d93231, d112431, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d93231, d112431, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d93232 q = 1) (hb : d112432 q = 1) : d0 q = 1 := by
    cases bit : q 255 with
    | false =>
      simp only [d93232, d112432, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d93232, d112432, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d93233 q = 1) (hb : d112433 q = 1) : d0 q = 1 := by
    cases bit : q 254 with
    | false =>
      simp only [d93233, d112433, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d93233, d112433, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro17695 (p : Pattern) (ha : d93239 p = 1) (hb : d112439 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d93234 q = 1) (hb : d112434 q = 1) : d0 q = 1 := by
    cases bit : q 253 with
    | false =>
      simp only [d93234, d112434, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17694 q ha hb
    | true =>
      simp only [d93234, d112434, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d93235 q = 1) (hb : d112435 q = 1) : d0 q = 1 := by
    cases bit : q 252 with
    | false =>
      simp only [d93235, d112435, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d93235, d112435, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d93236 q = 1) (hb : d112436 q = 1) : d0 q = 1 := by
    cases bit : q 251 with
    | false =>
      simp only [d93236, d112436, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d93236, d112436, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d93237 q = 1) (hb : d112437 q = 1) : d0 q = 1 := by
    cases bit : q 250 with
    | false =>
      simp only [d93237, d112437, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d93237, d112437, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d93238 q = 1) (hb : d112438 q = 1) : d0 q = 1 := by
    cases bit : q 249 with
    | false =>
      simp only [d93238, d112438, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d93238, d112438, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d93239 q = 1) (hb : d112439 q = 1) : d0 q = 1 := by
    cases bit : q 245 with
    | false =>
      simp only [d93239, d112439, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d93239, d112439, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro17696 (p : Pattern) (ha : d93245 p = 1) (hb : d112445 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d93240 q = 1) (hb : d112440 q = 1) : d0 q = 1 := by
    cases bit : q 200 with
    | false =>
      simp only [d93240, d112440, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17695 q ha hb
    | true =>
      simp only [d93240, d112440, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d93241 q = 1) (hb : d112441 q = 1) : d0 q = 1 := by
    cases bit : q 199 with
    | false =>
      simp only [d93241, d112441, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d93241, d112441, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d93242 q = 1) (hb : d112442 q = 1) : d0 q = 1 := by
    cases bit : q 186 with
    | false =>
      simp only [d93242, d112442, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d93242, d112442, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d93243 q = 1) (hb : d112443 q = 1) : d0 q = 1 := by
    cases bit : q 185 with
    | false =>
      simp only [d93243, d112443, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d93243, d112443, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d93244 q = 1) (hb : d112444 q = 1) : d0 q = 1 := by
    cases bit : q 184 with
    | false =>
      simp only [d93244, d112444, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d93244, d112444, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d93245 q = 1) (hb : d112445 q = 1) : d0 q = 1 := by
    cases bit : q 181 with
    | false =>
      simp only [d93245, d112445, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d93245, d112445, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro17697 (p : Pattern) (ha : d93251 p = 1) (hb : d112451 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d93246 q = 1) (hb : d112446 q = 1) : d0 q = 1 := by
    cases bit : q 177 with
    | false =>
      simp only [d93246, d112446, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17696 q ha hb
    | true =>
      simp only [d93246, d112446, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d93247 q = 1) (hb : d112447 q = 1) : d0 q = 1 := by
    cases bit : q 164 with
    | false =>
      simp only [d93247, d112447, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d93247, d112447, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d93248 q = 1) (hb : d112448 q = 1) : d0 q = 1 := by
    cases bit : q 156 with
    | false =>
      simp only [d93248, d112448, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d93248, d112448, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d93249 q = 1) (hb : d112449 q = 1) : d0 q = 1 := by
    cases bit : q 155 with
    | false =>
      simp only [d93249, d112449, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d93249, d112449, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d93250 q = 1) (hb : d112450 q = 1) : d0 q = 1 := by
    cases bit : q 134 with
    | false =>
      simp only [d93250, d112450, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d93250, d112450, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d93251 q = 1) (hb : d112451 q = 1) : d0 q = 1 := by
    cases bit : q 133 with
    | false =>
      simp only [d93251, d112451, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d93251, d112451, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro17698 (p : Pattern) (ha : d93257 p = 1) (hb : d112457 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d93252 q = 1) (hb : d112452 q = 1) : d0 q = 1 := by
    cases bit : q 120 with
    | false =>
      simp only [d93252, d112452, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17697 q ha hb
    | true =>
      simp only [d93252, d112452, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d93253 q = 1) (hb : d112453 q = 1) : d0 q = 1 := by
    cases bit : q 118 with
    | false =>
      simp only [d93253, d112453, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d93253, d112453, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d93254 q = 1) (hb : d112454 q = 1) : d0 q = 1 := by
    cases bit : q 114 with
    | false =>
      simp only [d93254, d112454, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d93254, d112454, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d93255 q = 1) (hb : d112455 q = 1) : d0 q = 1 := by
    cases bit : q 111 with
    | false =>
      simp only [d93255, d112455, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d93255, d112455, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d93256 q = 1) (hb : d112456 q = 1) : d0 q = 1 := by
    cases bit : q 98 with
    | false =>
      simp only [d93256, d112456, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d93256, d112456, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d93257 q = 1) (hb : d112457 q = 1) : d0 q = 1 := by
    cases bit : q 97 with
    | false =>
      simp only [d93257, d112457, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d93257, d112457, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro17699 (p : Pattern) (ha : d93263 p = 1) (hb : d112463 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d93258 q = 1) (hb : d112458 q = 1) : d0 q = 1 := by
    cases bit : q 94 with
    | false =>
      simp only [d93258, d112458, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17698 q ha hb
    | true =>
      simp only [d93258, d112458, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d93259 q = 1) (hb : d112459 q = 1) : d0 q = 1 := by
    cases bit : q 76 with
    | false =>
      simp only [d93259, d112459, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d93259, d112459, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d93260 q = 1) (hb : d112460 q = 1) : d0 q = 1 := by
    cases bit : q 67 with
    | false =>
      simp only [d93260, d112460, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d93260, d112460, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d93261 q = 1) (hb : d112461 q = 1) : d0 q = 1 := by
    cases bit : q 52 with
    | false =>
      simp only [d93261, d112461, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d93261, d112461, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d93262 q = 1) (hb : d112462 q = 1) : d0 q = 1 := by
    cases bit : q 47 with
    | false =>
      simp only [d93262, d112462, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d93262, d112462, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d93263 q = 1) (hb : d112463 q = 1) : d0 q = 1 := by
    cases bit : q 46 with
    | false =>
      simp only [d93263, d112463, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d93263, d112463, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro17700 (p : Pattern) (ha : d93269 p = 1) (hb : d112469 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d93264 q = 1) (hb : d112464 q = 1) : d0 q = 1 := by
    cases bit : q 45 with
    | false =>
      simp only [d93264, d112464, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17699 q ha hb
    | true =>
      simp only [d93264, d112464, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d93265 q = 1) (hb : d112465 q = 1) : d0 q = 1 := by
    cases bit : q 30 with
    | false =>
      simp only [d93265, d112465, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d93265, d112465, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d93266 q = 1) (hb : d112466 q = 1) : d0 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d93266, d112466, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d93266, d112466, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d93267 q = 1) (hb : d112467 q = 1) : d0 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d93267, d112467, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d93267, d112467, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d93268 q = 1) (hb : d112468 q = 1) : d0 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d93268, d112468, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d93268, d112468, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d93269 q = 1) (hb : d112469 q = 1) : d0 q = 1 := by
    cases bit : q 25 with
    | false =>
      simp only [d93269, d112469, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d93269, d112469, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro17701 (p : Pattern) (ha : d92315 p = 1) (hb : d99199 p = 1) : d112472 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d92315 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d49 q = 1) (hb : d92315 q = 1) : d49 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d7255 q = 1) (hb : d92315 q = 1) : d111675 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7255, d111675, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17350 q ha hb
    | true =>
      simp only [d7255, d111675, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d7305 q = 1) (hb : d92315 q = 1) : d111721 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d7305, d111721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7305, d111721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d7306 q = 1) (hb : d92315 q = 1) : d111722 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d7306, d111722, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d7306, d111722, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d7307 q = 1) (hb : d92315 q = 1) : d111723 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d7307, d111723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7307, d111723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d7308 q = 1) (hb : d92315 q = 1) : d111724 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d7308, d111724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7308, d111724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d92315 q = 1) (hb : d99199 q = 1) : d112472 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d99199, d112472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d99199, d112472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  exact h7 p ha hb
theorem andIntro17702 (p : Pattern) (ha : d92315 p = 1) (hb : d99209 p = 1) : d112482 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d92315 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d83 q = 1) (hb : d92315 q = 1) : d83 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d7281 q = 1) (hb : d92315 q = 1) : d111697 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7281, d111697, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17354 q ha hb
    | true =>
      simp only [d7281, d111697, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d92315 q = 1) (hb : d99205 q = 1) : d112478 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d99205, d112478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d99205, d112478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d92315 q = 1) (hb : d99206 q = 1) : d112479 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d99206, d112479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d99206, d112479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d92315 q = 1) (hb : d99207 q = 1) : d112480 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d99207, d112480, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d99207, d112480, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d92315 q = 1) (hb : d99208 q = 1) : d112481 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d99208, d112481, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d99208, d112481, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d92315 q = 1) (hb : d99209 q = 1) : d112482 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d99209, d112482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d99209, d112482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro17703 (p : Pattern) (ha : d92315 p = 1) (hb : d99215 p = 1) : d112488 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d92315 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d7310 q = 1) (hb : d92315 q = 1) : d111726 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d7310, d111726, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17357 q ha hb
    | true =>
      simp only [d7310, d111726, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17358 q ha hb
  have h2 (q : Pattern) (ha : d7311 q = 1) (hb : d92315 q = 1) : d111727 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d7311, d111727, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d7311, d111727, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d92315 q = 1) (hb : d99197 q = 1) : d112470 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d99197, d112470, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d99197, d112470, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d92315 q = 1) (hb : d99198 q = 1) : d112471 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d99198, d112471, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d99198, d112471, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d92315 q = 1) (hb : d99200 q = 1) : d112473 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d99200, d112473, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d99200, d112473, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17701 q ha hb
  have h6 (q : Pattern) (ha : d92315 q = 1) (hb : d99201 q = 1) : d112474 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d99201, d112474, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d99201, d112474, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d92315 q = 1) (hb : d99202 q = 1) : d112475 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d99202, d112475, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d99202, d112475, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d92315 q = 1) (hb : d99203 q = 1) : d112476 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d99203, d112476, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d99203, d112476, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d92315 q = 1) (hb : d99204 q = 1) : d112477 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d99204, d112477, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d99204, d112477, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d92315 q = 1) (hb : d99210 q = 1) : d112483 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d99210, d112483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d99210, d112483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17702 q ha hb
  have h11 (q : Pattern) (ha : d92315 q = 1) (hb : d99211 q = 1) : d112484 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d99211, d112484, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d99211, d112484, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d92315 q = 1) (hb : d99212 q = 1) : d112485 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d99212, d112485, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d99212, d112485, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d92315 q = 1) (hb : d99213 q = 1) : d112486 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d99213, d112486, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d99213, d112486, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h14 (q : Pattern) (ha : d92315 q = 1) (hb : d99214 q = 1) : d112487 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d99214, d112487, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d99214, d112487, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h15 (q : Pattern) (ha : d92315 q = 1) (hb : d99215 q = 1) : d112488 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d99215, d112488, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d99215, d112488, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro17704 (p : Pattern) (ha : d92315 p = 1) (hb : d99221 p = 1) : d112494 p = 1 := by
  have h0 (q : Pattern) (ha : d53652 q = 1) (hb : d92315 q = 1) : d53652 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d92315 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d92315 q = 1) (hb : d99216 q = 1) : d112489 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d99216, d112489, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d99216, d112489, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17703 q ha hb
  have h3 (q : Pattern) (ha : d92315 q = 1) (hb : d99217 q = 1) : d112490 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d99217, d112490, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d99217, d112490, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d92315 q = 1) (hb : d99218 q = 1) : d112491 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d99218, d112491, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d99218, d112491, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d92315 q = 1) (hb : d99219 q = 1) : d112492 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d99219, d112492, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d99219, d112492, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d92315 q = 1) (hb : d99220 q = 1) : d112493 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d99220, d112493, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d99220, d112493, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d92315 q = 1) (hb : d99221 q = 1) : d112494 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d99221, d112494, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d99221, d112494, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro17705 (p : Pattern) (ha : d92315 p = 1) (hb : d99224 p = 1) : d112497 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d92315 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d501 q = 1) (hb : d92315 q = 1) : d501 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d7443 q = 1) (hb : d92315 q = 1) : d111814 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7443, d111814, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17380 q ha hb
    | true =>
      simp only [d7443, d111814, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d7444 q = 1) (hb : d92315 q = 1) : d111815 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d7444, d111815, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7444, d111815, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d7445 q = 1) (hb : d92315 q = 1) : d111816 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d7445, d111816, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d7445, d111816, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d7446 q = 1) (hb : d92315 q = 1) : d111817 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d7446, d111817, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7446, d111817, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d7447 q = 1) (hb : d92315 q = 1) : d111818 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d7447, d111818, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7447, d111818, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d92315 q = 1) (hb : d99224 q = 1) : d112497 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d99224, d112497, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d99224, d112497, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  exact h7 p ha hb
theorem andIntro17706 (p : Pattern) (ha : d92315 p = 1) (hb : d99235 p = 1) : d112508 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d92315 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d730 q = 1) (hb : d92315 q = 1) : d730 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d92315 q = 1) (hb : d99230 q = 1) : d112503 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d99230, d112503, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17397 q hb ha
    | true =>
      simp only [d99230, d112503, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d92315 q = 1) (hb : d99231 q = 1) : d112504 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d99231, d112504, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d99231, d112504, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d92315 q = 1) (hb : d99232 q = 1) : d112505 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d99232, d112505, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d99232, d112505, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d92315 q = 1) (hb : d99233 q = 1) : d112506 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d99233, d112506, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d99233, d112506, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d92315 q = 1) (hb : d99234 q = 1) : d112507 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d99234, d112507, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d99234, d112507, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d92315 q = 1) (hb : d99235 q = 1) : d112508 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d99235, d112508, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d99235, d112508, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro17707 (p : Pattern) (ha : d92315 p = 1) (hb : d99241 p = 1) : d112514 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d92315 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d7449 q = 1) (hb : d92315 q = 1) : d111820 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d7449, d111820, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17379 q ha hb
    | true =>
      simp only [d7449, d111820, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17381 q ha hb
  have h2 (q : Pattern) (ha : d7450 q = 1) (hb : d92315 q = 1) : d111821 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d7450, d111821, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d7450, d111821, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d92315 q = 1) (hb : d99222 q = 1) : d112495 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d99222, d112495, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d99222, d112495, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d92315 q = 1) (hb : d99223 q = 1) : d112496 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d99223, d112496, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d99223, d112496, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d92315 q = 1) (hb : d99225 q = 1) : d112498 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d99225, d112498, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d99225, d112498, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17705 q ha hb
  have h6 (q : Pattern) (ha : d92315 q = 1) (hb : d99226 q = 1) : d112499 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d99226, d112499, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d99226, d112499, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d92315 q = 1) (hb : d99227 q = 1) : d112500 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d99227, d112500, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d99227, d112500, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d92315 q = 1) (hb : d99228 q = 1) : d112501 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d99228, d112501, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d99228, d112501, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d92315 q = 1) (hb : d99229 q = 1) : d112502 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d99229, d112502, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d99229, d112502, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d92315 q = 1) (hb : d99236 q = 1) : d112509 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d99236, d112509, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d99236, d112509, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17706 q ha hb
  have h11 (q : Pattern) (ha : d92315 q = 1) (hb : d99237 q = 1) : d112510 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d99237, d112510, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d99237, d112510, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d92315 q = 1) (hb : d99238 q = 1) : d112511 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d99238, d112511, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d99238, d112511, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d92315 q = 1) (hb : d99239 q = 1) : d112512 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d99239, d112512, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d99239, d112512, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h14 (q : Pattern) (ha : d92315 q = 1) (hb : d99240 q = 1) : d112513 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d99240, d112513, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d99240, d112513, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h15 (q : Pattern) (ha : d92315 q = 1) (hb : d99241 q = 1) : d112514 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d99241, d112514, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d99241, d112514, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro17708 (p : Pattern) (ha : d92315 p = 1) (hb : d99247 p = 1) : d112520 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d92315 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d92315 q = 1) (hb : d99242 q = 1) : d112515 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d99242, d112515, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d99242, d112515, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17707 q ha hb
  have h2 (q : Pattern) (ha : d92315 q = 1) (hb : d99243 q = 1) : d112516 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d99243, d112516, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d99243, d112516, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d92315 q = 1) (hb : d99244 q = 1) : d112517 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d99244, d112517, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d99244, d112517, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d92315 q = 1) (hb : d99245 q = 1) : d112518 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d99245, d112518, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d99245, d112518, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d92315 q = 1) (hb : d99246 q = 1) : d112519 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d99246, d112519, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d99246, d112519, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d92315 q = 1) (hb : d99247 q = 1) : d112520 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d99247, d112520, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d99247, d112520, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro17709 (p : Pattern) (ha : d92315 p = 1) (hb : d99251 p = 1) : d112524 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d92315 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d793 q = 1) (hb : d92315 q = 1) : d793 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d7591 q = 1) (hb : d92315 q = 1) : d111934 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7591, d111934, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17405 q ha hb
    | true =>
      simp only [d7591, d111934, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d7592 q = 1) (hb : d92315 q = 1) : d111935 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d7592, d111935, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7592, d111935, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d7593 q = 1) (hb : d92315 q = 1) : d111936 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d7593, d111936, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d7593, d111936, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d7594 q = 1) (hb : d92315 q = 1) : d111937 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d7594, d111937, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7594, d111937, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d7595 q = 1) (hb : d92315 q = 1) : d111938 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d7595, d111938, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7595, d111938, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d92315 q = 1) (hb : d99251 q = 1) : d112524 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d99251, d112524, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d99251, d112524, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  exact h7 p ha hb
theorem andIntro17710 (p : Pattern) (ha : d92315 p = 1) (hb : d99262 p = 1) : d112535 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d92315 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1063 q = 1) (hb : d92315 q = 1) : d1063 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d92315 q = 1) (hb : d99257 q = 1) : d112530 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d99257, d112530, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17423 q hb ha
    | true =>
      simp only [d99257, d112530, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d92315 q = 1) (hb : d99258 q = 1) : d112531 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d99258, d112531, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d99258, d112531, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d92315 q = 1) (hb : d99259 q = 1) : d112532 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d99259, d112532, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d99259, d112532, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d92315 q = 1) (hb : d99260 q = 1) : d112533 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d99260, d112533, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d99260, d112533, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d92315 q = 1) (hb : d99261 q = 1) : d112534 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d99261, d112534, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d99261, d112534, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d92315 q = 1) (hb : d99262 q = 1) : d112535 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d99262, d112535, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d99262, d112535, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro17711 (p : Pattern) (ha : d92315 p = 1) (hb : d99268 p = 1) : d112541 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d92315 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d7597 q = 1) (hb : d92315 q = 1) : d111940 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d7597, d111940, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17404 q ha hb
    | true =>
      simp only [d7597, d111940, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17406 q ha hb
  have h2 (q : Pattern) (ha : d7598 q = 1) (hb : d92315 q = 1) : d111941 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d7598, d111941, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d7598, d111941, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d92315 q = 1) (hb : d99249 q = 1) : d112522 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d99249, d112522, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d99249, d112522, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d92315 q = 1) (hb : d99250 q = 1) : d112523 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d99250, d112523, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d99250, d112523, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d92315 q = 1) (hb : d99252 q = 1) : d112525 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d99252, d112525, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d99252, d112525, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17709 q ha hb
  have h6 (q : Pattern) (ha : d92315 q = 1) (hb : d99253 q = 1) : d112526 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d99253, d112526, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d99253, d112526, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d92315 q = 1) (hb : d99254 q = 1) : d112527 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d99254, d112527, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d99254, d112527, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d92315 q = 1) (hb : d99255 q = 1) : d112528 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d99255, d112528, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d99255, d112528, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d92315 q = 1) (hb : d99256 q = 1) : d112529 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d99256, d112529, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d99256, d112529, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d92315 q = 1) (hb : d99263 q = 1) : d112536 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d99263, d112536, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d99263, d112536, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17710 q ha hb
  have h11 (q : Pattern) (ha : d92315 q = 1) (hb : d99264 q = 1) : d112537 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d99264, d112537, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d99264, d112537, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d92315 q = 1) (hb : d99265 q = 1) : d112538 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d99265, d112538, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d99265, d112538, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d92315 q = 1) (hb : d99266 q = 1) : d112539 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d99266, d112539, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d99266, d112539, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h14 (q : Pattern) (ha : d92315 q = 1) (hb : d99267 q = 1) : d112540 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d99267, d112540, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d99267, d112540, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h15 (q : Pattern) (ha : d92315 q = 1) (hb : d99268 q = 1) : d112541 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d99268, d112541, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d99268, d112541, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro17712 (p : Pattern) (ha : d92315 p = 1) (hb : d99274 p = 1) : d112547 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d92315 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d92315 q = 1) (hb : d99269 q = 1) : d112542 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d99269, d112542, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d99269, d112542, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17711 q ha hb
  have h2 (q : Pattern) (ha : d92315 q = 1) (hb : d99270 q = 1) : d112543 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d99270, d112543, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d99270, d112543, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d92315 q = 1) (hb : d99271 q = 1) : d112544 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d99271, d112544, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d99271, d112544, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d92315 q = 1) (hb : d99272 q = 1) : d112545 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d99272, d112545, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d99272, d112545, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d92315 q = 1) (hb : d99273 q = 1) : d112546 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d99273, d112546, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d99273, d112546, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d92315 q = 1) (hb : d99274 q = 1) : d112547 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d99274, d112547, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d99274, d112547, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro17713 (p : Pattern) (ha : d92315 p = 1) (hb : d99279 p = 1) : d112552 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d92315 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1172 q = 1) (hb : d92315 q = 1) : d1172 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d7744 q = 1) (hb : d92315 q = 1) : d112059 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7744, d112059, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17431 q ha hb
    | true =>
      simp only [d7744, d112059, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d7745 q = 1) (hb : d92315 q = 1) : d112060 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d7745, d112060, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7745, d112060, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d7746 q = 1) (hb : d92315 q = 1) : d112061 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d7746, d112061, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d7746, d112061, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d7747 q = 1) (hb : d92315 q = 1) : d112062 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d7747, d112062, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7747, d112062, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d7748 q = 1) (hb : d92315 q = 1) : d112063 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d7748, d112063, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7748, d112063, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d92315 q = 1) (hb : d99279 q = 1) : d112552 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d99279, d112552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d99279, d112552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  exact h7 p ha hb
theorem andIntro17714 (p : Pattern) (ha : d92315 p = 1) (hb : d99290 p = 1) : d112563 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d92315 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1497 q = 1) (hb : d92315 q = 1) : d1497 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d92315 q = 1) (hb : d99285 q = 1) : d112558 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d99285, d112558, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17449 q hb ha
    | true =>
      simp only [d99285, d112558, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d92315 q = 1) (hb : d99286 q = 1) : d112559 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d99286, d112559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d99286, d112559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d92315 q = 1) (hb : d99287 q = 1) : d112560 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d99287, d112560, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d99287, d112560, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d92315 q = 1) (hb : d99288 q = 1) : d112561 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d99288, d112561, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d99288, d112561, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d92315 q = 1) (hb : d99289 q = 1) : d112562 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d99289, d112562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d99289, d112562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d92315 q = 1) (hb : d99290 q = 1) : d112563 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d99290, d112563, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d99290, d112563, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro17715 (p : Pattern) (ha : d92315 p = 1) (hb : d99296 p = 1) : d112569 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d92315 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d7750 q = 1) (hb : d92315 q = 1) : d112065 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d7750, d112065, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17430 q ha hb
    | true =>
      simp only [d7750, d112065, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17432 q ha hb
  have h2 (q : Pattern) (ha : d7751 q = 1) (hb : d92315 q = 1) : d112066 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d7751, d112066, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d7751, d112066, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d92315 q = 1) (hb : d99277 q = 1) : d112550 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d99277, d112550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d99277, d112550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d92315 q = 1) (hb : d99278 q = 1) : d112551 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d99278, d112551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d99278, d112551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d92315 q = 1) (hb : d99280 q = 1) : d112553 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d99280, d112553, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d99280, d112553, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17713 q ha hb
  have h6 (q : Pattern) (ha : d92315 q = 1) (hb : d99281 q = 1) : d112554 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d99281, d112554, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d99281, d112554, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d92315 q = 1) (hb : d99282 q = 1) : d112555 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d99282, d112555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d99282, d112555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d92315 q = 1) (hb : d99283 q = 1) : d112556 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d99283, d112556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d99283, d112556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d92315 q = 1) (hb : d99284 q = 1) : d112557 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d99284, d112557, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d99284, d112557, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d92315 q = 1) (hb : d99291 q = 1) : d112564 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d99291, d112564, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d99291, d112564, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17714 q ha hb
  have h11 (q : Pattern) (ha : d92315 q = 1) (hb : d99292 q = 1) : d112565 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d99292, d112565, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d99292, d112565, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d92315 q = 1) (hb : d99293 q = 1) : d112566 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d99293, d112566, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d99293, d112566, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d92315 q = 1) (hb : d99294 q = 1) : d112567 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d99294, d112567, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d99294, d112567, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h14 (q : Pattern) (ha : d92315 q = 1) (hb : d99295 q = 1) : d112568 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d99295, d112568, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d99295, d112568, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h15 (q : Pattern) (ha : d92315 q = 1) (hb : d99296 q = 1) : d112569 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d99296, d112569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d99296, d112569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro17716 (p : Pattern) (ha : d92315 p = 1) (hb : d99302 p = 1) : d112575 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d92315 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d92315 q = 1) (hb : d99297 q = 1) : d112570 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d99297, d112570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d99297, d112570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17715 q ha hb
  have h2 (q : Pattern) (ha : d92315 q = 1) (hb : d99298 q = 1) : d112571 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d99298, d112571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d99298, d112571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d92315 q = 1) (hb : d99299 q = 1) : d112572 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d99299, d112572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d99299, d112572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d92315 q = 1) (hb : d99300 q = 1) : d112573 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d99300, d112573, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d99300, d112573, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d92315 q = 1) (hb : d99301 q = 1) : d112574 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d99301, d112574, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d99301, d112574, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d92315 q = 1) (hb : d99302 q = 1) : d112575 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d99302, d112575, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d99302, d112575, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro17717 (p : Pattern) (ha : d92315 p = 1) (hb : d99308 p = 1) : d112581 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d92315 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1633 q = 1) (hb : d92315 q = 1) : d1633 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d7898 q = 1) (hb : d92315 q = 1) : d112185 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7898, d112185, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17457 q ha hb
    | true =>
      simp only [d7898, d112185, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d7899 q = 1) (hb : d92315 q = 1) : d112186 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d7899, d112186, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7899, d112186, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d7900 q = 1) (hb : d92315 q = 1) : d112187 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d7900, d112187, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d7900, d112187, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d7901 q = 1) (hb : d92315 q = 1) : d112188 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d7901, d112188, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7901, d112188, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d7902 q = 1) (hb : d92315 q = 1) : d112189 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d7902, d112189, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7902, d112189, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d92315 q = 1) (hb : d99308 q = 1) : d112581 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d99308, d112581, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d99308, d112581, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  exact h7 p ha hb
theorem andIntro17718 (p : Pattern) (ha : d92315 p = 1) (hb : d99319 p = 1) : d112592 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d92315 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1974 q = 1) (hb : d92315 q = 1) : d1974 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d92315 q = 1) (hb : d99314 q = 1) : d112587 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d99314, d112587, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17475 q hb ha
    | true =>
      simp only [d99314, d112587, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d92315 q = 1) (hb : d99315 q = 1) : d112588 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d99315, d112588, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d99315, d112588, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d92315 q = 1) (hb : d99316 q = 1) : d112589 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d99316, d112589, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d99316, d112589, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d92315 q = 1) (hb : d99317 q = 1) : d112590 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d99317, d112590, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d99317, d112590, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d92315 q = 1) (hb : d99318 q = 1) : d112591 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d99318, d112591, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d99318, d112591, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d92315 q = 1) (hb : d99319 q = 1) : d112592 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d99319, d112592, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d99319, d112592, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro17719 (p : Pattern) (ha : d92315 p = 1) (hb : d99325 p = 1) : d112598 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d92315 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d7904 q = 1) (hb : d92315 q = 1) : d112191 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d7904, d112191, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17456 q ha hb
    | true =>
      simp only [d7904, d112191, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17458 q ha hb
  have h2 (q : Pattern) (ha : d7905 q = 1) (hb : d92315 q = 1) : d112192 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d7905, d112192, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d7905, d112192, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d92315 q = 1) (hb : d99306 q = 1) : d112579 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d99306, d112579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d99306, d112579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d92315 q = 1) (hb : d99307 q = 1) : d112580 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d99307, d112580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d99307, d112580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d92315 q = 1) (hb : d99309 q = 1) : d112582 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d99309, d112582, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d99309, d112582, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17717 q ha hb
  have h6 (q : Pattern) (ha : d92315 q = 1) (hb : d99310 q = 1) : d112583 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d99310, d112583, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d99310, d112583, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d92315 q = 1) (hb : d99311 q = 1) : d112584 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d99311, d112584, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d99311, d112584, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d92315 q = 1) (hb : d99312 q = 1) : d112585 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d99312, d112585, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d99312, d112585, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d92315 q = 1) (hb : d99313 q = 1) : d112586 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d99313, d112586, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d99313, d112586, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d92315 q = 1) (hb : d99320 q = 1) : d112593 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d99320, d112593, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d99320, d112593, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17718 q ha hb
  have h11 (q : Pattern) (ha : d92315 q = 1) (hb : d99321 q = 1) : d112594 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d99321, d112594, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d99321, d112594, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d92315 q = 1) (hb : d99322 q = 1) : d112595 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d99322, d112595, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d99322, d112595, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d92315 q = 1) (hb : d99323 q = 1) : d112596 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d99323, d112596, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d99323, d112596, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h14 (q : Pattern) (ha : d92315 q = 1) (hb : d99324 q = 1) : d112597 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d99324, d112597, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d99324, d112597, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h15 (q : Pattern) (ha : d92315 q = 1) (hb : d99325 q = 1) : d112598 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d99325, d112598, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d99325, d112598, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro17720 (p : Pattern) (ha : d92315 p = 1) (hb : d99331 p = 1) : d112604 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d92315 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d92315 q = 1) (hb : d99326 q = 1) : d112599 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d99326, d112599, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d99326, d112599, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17719 q ha hb
  have h2 (q : Pattern) (ha : d92315 q = 1) (hb : d99327 q = 1) : d112600 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d99327, d112600, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d99327, d112600, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d92315 q = 1) (hb : d99328 q = 1) : d112601 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d99328, d112601, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d99328, d112601, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d92315 q = 1) (hb : d99329 q = 1) : d112602 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d99329, d112602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d99329, d112602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d92315 q = 1) (hb : d99330 q = 1) : d112603 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d99330, d112603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d99330, d112603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d92315 q = 1) (hb : d99331 q = 1) : d112604 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d99331, d112604, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d99331, d112604, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro17721 (p : Pattern) (ha : d92315 p = 1) (hb : d99338 p = 1) : d112611 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d92315 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d2116 q = 1) (hb : d92315 q = 1) : d2116 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d8053 q = 1) (hb : d92315 q = 1) : d112312 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d8053, d112312, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17483 q ha hb
    | true =>
      simp only [d8053, d112312, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d8054 q = 1) (hb : d92315 q = 1) : d112313 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d8054, d112313, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8054, d112313, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d8055 q = 1) (hb : d92315 q = 1) : d112314 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d8055, d112314, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d8055, d112314, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d8056 q = 1) (hb : d92315 q = 1) : d112315 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d8056, d112315, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8056, d112315, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d8057 q = 1) (hb : d92315 q = 1) : d112316 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d8057, d112316, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8057, d112316, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d92315 q = 1) (hb : d99338 q = 1) : d112611 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d99338, d112611, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d99338, d112611, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  exact h7 p ha hb
theorem andIntro17722 (p : Pattern) (ha : d92315 p = 1) (hb : d99349 p = 1) : d112622 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d92315 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d2452 q = 1) (hb : d92315 q = 1) : d2452 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d92315 q = 1) (hb : d99344 q = 1) : d112617 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d99344, d112617, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17501 q hb ha
    | true =>
      simp only [d99344, d112617, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d92315 q = 1) (hb : d99345 q = 1) : d112618 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d99345, d112618, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d99345, d112618, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d92315 q = 1) (hb : d99346 q = 1) : d112619 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d99346, d112619, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d99346, d112619, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d92315 q = 1) (hb : d99347 q = 1) : d112620 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d99347, d112620, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d99347, d112620, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d92315 q = 1) (hb : d99348 q = 1) : d112621 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d99348, d112621, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d99348, d112621, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d92315 q = 1) (hb : d99349 q = 1) : d112622 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d99349, d112622, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d99349, d112622, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro17723 (p : Pattern) (ha : d92315 p = 1) (hb : d99355 p = 1) : d112628 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d92315 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d8059 q = 1) (hb : d92315 q = 1) : d112318 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d8059, d112318, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17482 q ha hb
    | true =>
      simp only [d8059, d112318, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17484 q ha hb
  have h2 (q : Pattern) (ha : d8060 q = 1) (hb : d92315 q = 1) : d112319 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d8060, d112319, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d8060, d112319, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d92315 q = 1) (hb : d99336 q = 1) : d112609 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d99336, d112609, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d99336, d112609, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d92315 q = 1) (hb : d99337 q = 1) : d112610 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d99337, d112610, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d99337, d112610, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d92315 q = 1) (hb : d99339 q = 1) : d112612 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d99339, d112612, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d99339, d112612, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17721 q ha hb
  have h6 (q : Pattern) (ha : d92315 q = 1) (hb : d99340 q = 1) : d112613 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d99340, d112613, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d99340, d112613, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d92315 q = 1) (hb : d99341 q = 1) : d112614 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d99341, d112614, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d99341, d112614, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d92315 q = 1) (hb : d99342 q = 1) : d112615 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d99342, d112615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d99342, d112615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d92315 q = 1) (hb : d99343 q = 1) : d112616 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d99343, d112616, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d99343, d112616, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d92315 q = 1) (hb : d99350 q = 1) : d112623 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d99350, d112623, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d99350, d112623, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17722 q ha hb
  have h11 (q : Pattern) (ha : d92315 q = 1) (hb : d99351 q = 1) : d112624 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d99351, d112624, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d99351, d112624, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d92315 q = 1) (hb : d99352 q = 1) : d112625 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d99352, d112625, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d99352, d112625, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d92315 q = 1) (hb : d99353 q = 1) : d112626 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d99353, d112626, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d99353, d112626, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h14 (q : Pattern) (ha : d92315 q = 1) (hb : d99354 q = 1) : d112627 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d99354, d112627, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d99354, d112627, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h15 (q : Pattern) (ha : d92315 q = 1) (hb : d99355 q = 1) : d112628 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d99355, d112628, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d99355, d112628, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro17724 (p : Pattern) (ha : d92315 p = 1) (hb : d99361 p = 1) : d112634 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d92315 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d92315 q = 1) (hb : d99356 q = 1) : d112629 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d99356, d112629, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d99356, d112629, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17723 q ha hb
  have h2 (q : Pattern) (ha : d92315 q = 1) (hb : d99357 q = 1) : d112630 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d99357, d112630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d99357, d112630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d92315 q = 1) (hb : d99358 q = 1) : d112631 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d99358, d112631, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d99358, d112631, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d92315 q = 1) (hb : d99359 q = 1) : d112632 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d99359, d112632, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d99359, d112632, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d92315 q = 1) (hb : d99360 q = 1) : d112633 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d99360, d112633, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d99360, d112633, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d92315 q = 1) (hb : d99361 q = 1) : d112634 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d99361, d112634, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d99361, d112634, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro17725 (p : Pattern) (ha : d92315 p = 1) (hb : d99367 p = 1) : d112640 p = 1 := by
  have h0 (q : Pattern) (ha : d92315 q = 1) (hb : d99248 q = 1) : d112521 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d99248, d112521, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17704 q ha hb
    | true =>
      simp only [d99248, d112521, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17708 q ha hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d92315 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d92315 q = 1) (hb : d99275 q = 1) : d112548 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d99275, d112548, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d99275, d112548, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17712 q ha hb
  have h3 (q : Pattern) (ha : d92315 q = 1) (hb : d99276 q = 1) : d112549 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d99276, d112549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d99276, d112549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d92315 q = 1) (hb : d99303 q = 1) : d112576 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d99303, d112576, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d99303, d112576, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17716 q ha hb
  have h5 (q : Pattern) (ha : d92315 q = 1) (hb : d99304 q = 1) : d112577 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d99304, d112577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d99304, d112577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d92315 q = 1) (hb : d99305 q = 1) : d112578 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d99305, d112578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d99305, d112578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d92315 q = 1) (hb : d99332 q = 1) : d112605 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d99332, d112605, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d99332, d112605, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17720 q ha hb
  have h8 (q : Pattern) (ha : d92315 q = 1) (hb : d99333 q = 1) : d112606 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d99333, d112606, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d99333, d112606, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d92315 q = 1) (hb : d99334 q = 1) : d112607 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d99334, d112607, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d99334, d112607, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d92315 q = 1) (hb : d99335 q = 1) : d112608 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d99335, d112608, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d99335, d112608, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d92315 q = 1) (hb : d99362 q = 1) : d112635 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d99362, d112635, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d99362, d112635, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17724 q ha hb
  have h12 (q : Pattern) (ha : d92315 q = 1) (hb : d99363 q = 1) : d112636 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d99363, d112636, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d99363, d112636, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d92315 q = 1) (hb : d99364 q = 1) : d112637 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d99364, d112637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d99364, d112637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d92315 q = 1) (hb : d99365 q = 1) : d112638 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d99365, d112638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d99365, d112638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d92315 q = 1) (hb : d99366 q = 1) : d112639 q = 1 := by
    cases bit : q 10250 with
    | false =>
      simp only [d99366, d112639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d99366, d112639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d92315 q = 1) (hb : d99367 q = 1) : d112640 q = 1 := by
    cases bit : q 260 with
    | false =>
      simp only [d99367, d112640, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d99367, d112640, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  exact h16 p ha hb
theorem andIntro17726 (p : Pattern) (ha : d92315 p = 1) (hb : d99373 p = 1) : d112646 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d92315 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d92315 q = 1) (hb : d99368 q = 1) : d112641 q = 1 := by
    cases bit : q 259 with
    | false =>
      simp only [d99368, d112641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17725 q ha hb
    | true =>
      simp only [d99368, d112641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d92315 q = 1) (hb : d99369 q = 1) : d112642 q = 1 := by
    cases bit : q 258 with
    | false =>
      simp only [d99369, d112642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d99369, d112642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d92315 q = 1) (hb : d99370 q = 1) : d112643 q = 1 := by
    cases bit : q 257 with
    | false =>
      simp only [d99370, d112643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d99370, d112643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d92315 q = 1) (hb : d99371 q = 1) : d112644 q = 1 := by
    cases bit : q 256 with
    | false =>
      simp only [d99371, d112644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d99371, d112644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d92315 q = 1) (hb : d99372 q = 1) : d112645 q = 1 := by
    cases bit : q 255 with
    | false =>
      simp only [d99372, d112645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d99372, d112645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d92315 q = 1) (hb : d99373 q = 1) : d112646 q = 1 := by
    cases bit : q 254 with
    | false =>
      simp only [d99373, d112646, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d99373, d112646, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro17727 (p : Pattern) (ha : d92315 p = 1) (hb : d99379 p = 1) : d112652 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d92315 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d92315 q = 1) (hb : d99374 q = 1) : d112647 q = 1 := by
    cases bit : q 253 with
    | false =>
      simp only [d99374, d112647, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17726 q ha hb
    | true =>
      simp only [d99374, d112647, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d92315 q = 1) (hb : d99375 q = 1) : d112648 q = 1 := by
    cases bit : q 252 with
    | false =>
      simp only [d99375, d112648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d99375, d112648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d92315 q = 1) (hb : d99376 q = 1) : d112649 q = 1 := by
    cases bit : q 251 with
    | false =>
      simp only [d99376, d112649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d99376, d112649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d92315 q = 1) (hb : d99377 q = 1) : d112650 q = 1 := by
    cases bit : q 250 with
    | false =>
      simp only [d99377, d112650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d99377, d112650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d92315 q = 1) (hb : d99378 q = 1) : d112651 q = 1 := by
    cases bit : q 249 with
    | false =>
      simp only [d99378, d112651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d99378, d112651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d92315 q = 1) (hb : d99379 q = 1) : d112652 q = 1 := by
    cases bit : q 245 with
    | false =>
      simp only [d99379, d112652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d99379, d112652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro17728 (p : Pattern) (ha : d92315 p = 1) (hb : d99385 p = 1) : d112658 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d92315 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d92315 q = 1) (hb : d99380 q = 1) : d112653 q = 1 := by
    cases bit : q 200 with
    | false =>
      simp only [d99380, d112653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17727 q ha hb
    | true =>
      simp only [d99380, d112653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d92315 q = 1) (hb : d99381 q = 1) : d112654 q = 1 := by
    cases bit : q 199 with
    | false =>
      simp only [d99381, d112654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d99381, d112654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d92315 q = 1) (hb : d99382 q = 1) : d112655 q = 1 := by
    cases bit : q 186 with
    | false =>
      simp only [d99382, d112655, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d99382, d112655, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d92315 q = 1) (hb : d99383 q = 1) : d112656 q = 1 := by
    cases bit : q 185 with
    | false =>
      simp only [d99383, d112656, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d99383, d112656, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d92315 q = 1) (hb : d99384 q = 1) : d112657 q = 1 := by
    cases bit : q 184 with
    | false =>
      simp only [d99384, d112657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d99384, d112657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d92315 q = 1) (hb : d99385 q = 1) : d112658 q = 1 := by
    cases bit : q 181 with
    | false =>
      simp only [d99385, d112658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d99385, d112658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro17729 (p : Pattern) (ha : d92315 p = 1) (hb : d99391 p = 1) : d112664 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d92315 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d92315 q = 1) (hb : d99386 q = 1) : d112659 q = 1 := by
    cases bit : q 177 with
    | false =>
      simp only [d99386, d112659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17728 q ha hb
    | true =>
      simp only [d99386, d112659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d92315 q = 1) (hb : d99387 q = 1) : d112660 q = 1 := by
    cases bit : q 164 with
    | false =>
      simp only [d99387, d112660, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d99387, d112660, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d92315 q = 1) (hb : d99388 q = 1) : d112661 q = 1 := by
    cases bit : q 156 with
    | false =>
      simp only [d99388, d112661, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d99388, d112661, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d92315 q = 1) (hb : d99389 q = 1) : d112662 q = 1 := by
    cases bit : q 155 with
    | false =>
      simp only [d99389, d112662, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d99389, d112662, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d92315 q = 1) (hb : d99390 q = 1) : d112663 q = 1 := by
    cases bit : q 134 with
    | false =>
      simp only [d99390, d112663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d99390, d112663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d92315 q = 1) (hb : d99391 q = 1) : d112664 q = 1 := by
    cases bit : q 133 with
    | false =>
      simp only [d99391, d112664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d99391, d112664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro17730 (p : Pattern) (ha : d92315 p = 1) (hb : d99397 p = 1) : d112670 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d92315 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d92315 q = 1) (hb : d99392 q = 1) : d112665 q = 1 := by
    cases bit : q 120 with
    | false =>
      simp only [d99392, d112665, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17729 q ha hb
    | true =>
      simp only [d99392, d112665, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d92315 q = 1) (hb : d99393 q = 1) : d112666 q = 1 := by
    cases bit : q 118 with
    | false =>
      simp only [d99393, d112666, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d99393, d112666, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d92315 q = 1) (hb : d99394 q = 1) : d112667 q = 1 := by
    cases bit : q 114 with
    | false =>
      simp only [d99394, d112667, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d99394, d112667, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d92315 q = 1) (hb : d99395 q = 1) : d112668 q = 1 := by
    cases bit : q 111 with
    | false =>
      simp only [d99395, d112668, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d99395, d112668, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d92315 q = 1) (hb : d99396 q = 1) : d112669 q = 1 := by
    cases bit : q 98 with
    | false =>
      simp only [d99396, d112669, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d99396, d112669, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d92315 q = 1) (hb : d99397 q = 1) : d112670 q = 1 := by
    cases bit : q 97 with
    | false =>
      simp only [d99397, d112670, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d99397, d112670, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro17731 (p : Pattern) (ha : d92315 p = 1) (hb : d99403 p = 1) : d112676 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d92315 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d92315 q = 1) (hb : d99398 q = 1) : d112671 q = 1 := by
    cases bit : q 94 with
    | false =>
      simp only [d99398, d112671, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17730 q ha hb
    | true =>
      simp only [d99398, d112671, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d92315 q = 1) (hb : d99399 q = 1) : d112672 q = 1 := by
    cases bit : q 76 with
    | false =>
      simp only [d99399, d112672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d99399, d112672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d92315 q = 1) (hb : d99400 q = 1) : d112673 q = 1 := by
    cases bit : q 67 with
    | false =>
      simp only [d99400, d112673, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d99400, d112673, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d92315 q = 1) (hb : d99401 q = 1) : d112674 q = 1 := by
    cases bit : q 52 with
    | false =>
      simp only [d99401, d112674, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d99401, d112674, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d92315 q = 1) (hb : d99402 q = 1) : d112675 q = 1 := by
    cases bit : q 47 with
    | false =>
      simp only [d99402, d112675, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d99402, d112675, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d92315 q = 1) (hb : d99403 q = 1) : d112676 q = 1 := by
    cases bit : q 46 with
    | false =>
      simp only [d99403, d112676, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d99403, d112676, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro17732 (p : Pattern) (ha : d92315 p = 1) (hb : d99409 p = 1) : d112682 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d92315 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d92315 q = 1) (hb : d99404 q = 1) : d112677 q = 1 := by
    cases bit : q 45 with
    | false =>
      simp only [d99404, d112677, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17731 q ha hb
    | true =>
      simp only [d99404, d112677, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d92315 q = 1) (hb : d99405 q = 1) : d112678 q = 1 := by
    cases bit : q 30 with
    | false =>
      simp only [d99405, d112678, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d99405, d112678, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d92315 q = 1) (hb : d99406 q = 1) : d112679 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d99406, d112679, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d99406, d112679, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d92315 q = 1) (hb : d99407 q = 1) : d112680 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d99407, d112680, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d99407, d112680, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d92315 q = 1) (hb : d99408 q = 1) : d112681 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d99408, d112681, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d99408, d112681, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d92315 q = 1) (hb : d99409 q = 1) : d112682 q = 1 := by
    cases bit : q 25 with
    | false =>
      simp only [d99409, d112682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d99409, d112682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro17733 (p : Pattern) (ha : d92414 p = 1) (hb : d111718 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d92388 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d92394 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d92403 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d92322 q = 1) (hb : d111668 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d92322, d111668, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17515 q ha hb
    | true =>
      simp only [d92322, d111668, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5 q hb ha
  have h5 (q : Pattern) (ha : d92404 q = 1) (hb : d111714 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d92404, d111714, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d92404, d111714, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d92410 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d92411 q = 1) (hb : d111715 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d92411, d111715, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d92411, d111715, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d92412 q = 1) (hb : d111716 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d92412, d111716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d92412, d111716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d92413 q = 1) (hb : d111717 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d92413, d111717, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d92413, d111717, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d92414 q = 1) (hb : d111718 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d92414, d111718, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92414, d111718, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro17734 (p : Pattern) (ha : d92433 p = 1) (hb : d111725 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d92388 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d92394 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d92403 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d92322 q = 1) (hb : d111668 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d92322, d111668, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17515 q ha hb
    | true =>
      simp only [d92322, d111668, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5 q hb ha
  have h4 (q : Pattern) (ha : d92404 q = 1) (hb : d111714 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d92404, d111714, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d92404, d111714, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d92410 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d92411 q = 1) (hb : d111715 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d92411, d111715, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d92411, d111715, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d92412 q = 1) (hb : d111716 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d92412, d111716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d92412, d111716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d92413 q = 1) (hb : d111717 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d92413, d111717, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92413, d111717, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d92419 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d92423 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d92425 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d92329 q = 1) (hb : d111675 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d92329, d111675, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17517 q ha hb
    | true =>
      simp only [d92329, d111675, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7 q hb ha
  have h13 (q : Pattern) (ha : d92426 q = 1) (hb : d111721 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d92426, d111721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
    | true =>
      simp only [d92426, d111721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d92429 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d92430 q = 1) (hb : d111722 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d92430, d111722, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d92430, d111722, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d92431 q = 1) (hb : d111723 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d92431, d111723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
    | true =>
      simp only [d92431, d111723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d92432 q = 1) (hb : d111724 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d92432, d111724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
    | true =>
      simp only [d92432, d111724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d92433 q = 1) (hb : d111725 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d92433, d111725, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d92433, d111725, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro17735 (p : Pattern) (ha : d92442 p = 1) (hb : d112472 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d92425 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d92329 q = 1) (hb : d111675 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d92329, d111675, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17517 q ha hb
    | true =>
      simp only [d92329, d111675, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7 q hb ha
  have h3 (q : Pattern) (ha : d92426 q = 1) (hb : d111721 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d92426, d111721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d92426, d111721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d92429 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d92430 q = 1) (hb : d111722 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d92430, d111722, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d92430, d111722, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d92440 q = 1) (hb : d111723 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d92440, d111723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92440, d111723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d92441 q = 1) (hb : d111724 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d92441, d111724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92441, d111724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d92442 q = 1) (hb : d112472 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d92442, d112472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92442, d112472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro17736 (p : Pattern) (ha : d92467 p = 1) (hb : d112482 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d92456 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d92351 q = 1) (hb : d111697 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d92351, d111697, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17521 q ha hb
    | true =>
      simp only [d92351, d111697, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12 q hb ha
  have h3 (q : Pattern) (ha : d92457 q = 1) (hb : d112478 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d92457, d112478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d92457, d112478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d92463 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d92464 q = 1) (hb : d112479 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d92464, d112479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d92464, d112479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d92465 q = 1) (hb : d112480 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d92465, d112480, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92465, d112480, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d92466 q = 1) (hb : d112481 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d92466, d112481, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92466, d112481, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d92467 q = 1) (hb : d112482 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d92467, d112482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92467, d112482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro17737 (p : Pattern) (ha : d92473 p = 1) (hb : d112488 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d92382 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d92434 q = 1) (hb : d111726 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d92434, d111726, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17733 q ha hb
    | true =>
      simp only [d92434, d111726, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17734 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d92436 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d92437 q = 1) (hb : d111727 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d92437, d111727, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d92437, d111727, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d92438 q = 1) (hb : d112470 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d92438, d112470, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d92438, d112470, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d92439 q = 1) (hb : d112471 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d92439, d112471, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92439, d112471, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d92443 q = 1) (hb : d112473 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d92443, d112473, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d92443, d112473, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17735 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d52173 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d92444 q = 1) (hb : d112474 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d92444, d112474, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d92444, d112474, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d92445 q = 1) (hb : d112475 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d92445, d112475, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d92445, d112475, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h11 (q : Pattern) (ha : d92446 q = 1) (hb : d112476 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d92446, d112476, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d92446, d112476, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h12 (q : Pattern) (ha : d92447 q = 1) (hb : d112477 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d92447, d112477, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d92447, d112477, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d92468 q = 1) (hb : d112483 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d92468, d112483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d92468, d112483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17736 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d52210 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d92469 q = 1) (hb : d112484 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d92469, d112484, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d92469, d112484, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d92470 q = 1) (hb : d112485 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d92470, d112485, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d92470, d112485, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h17 (q : Pattern) (ha : d92471 q = 1) (hb : d112486 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d92471, d112486, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d92471, d112486, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h18 (q : Pattern) (ha : d92472 q = 1) (hb : d112487 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d92472, d112487, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d92472, d112487, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h19 (q : Pattern) (ha : d92473 q = 1) (hb : d112488 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d92473, d112488, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d92473, d112488, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro17738 (p : Pattern) (ha : d92479 p = 1) (hb : d112494 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d51951 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d53648 q = 1) (hb : d92363 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d53648, d92363, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d53648, d92363, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11594 q ha hb
  have h3 (q : Pattern) (ha : d53649 q = 1) (hb : d92364 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d53649, d92364, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d53649, d92364, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d53650 q = 1) (hb : d92365 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d53650, d92365, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d53650, d92365, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d53651 q = 1) (hb : d92366 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d53651, d92366, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d53651, d92366, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d53652 q = 1) (hb : d92367 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d53652, d92367, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53652, d92367, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d92474 q = 1) (hb : d112489 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d92474, d112489, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d92474, d112489, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17737 q ha hb
  have h8 (q : Pattern) (ha : d92475 q = 1) (hb : d112490 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d92475, d112490, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d92475, d112490, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d92476 q = 1) (hb : d112491 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d92476, d112491, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d92476, d112491, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d92477 q = 1) (hb : d112492 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d92477, d112492, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d92477, d112492, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d92478 q = 1) (hb : d112493 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d92478, d112493, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d92478, d112493, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d92479 q = 1) (hb : d112494 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d92479, d112494, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
    | true =>
      simp only [d92479, d112494, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  exact h12 p ha hb
theorem andIntro17739 (p : Pattern) (ha : d92538 p = 1) (hb : d111811 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d92507 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d92513 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d92527 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d92484 q = 1) (hb : d111806 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d92484, d111806, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17545 q ha hb
    | true =>
      simp only [d92484, d111806, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro63 q hb ha
  have h5 (q : Pattern) (ha : d92528 q = 1) (hb : d111807 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d92528, d111807, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d92528, d111807, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d92534 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d92535 q = 1) (hb : d111808 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d92535, d111808, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d92535, d111808, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d92536 q = 1) (hb : d111809 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d92536, d111809, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d92536, d111809, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d92537 q = 1) (hb : d111810 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d92537, d111810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d92537, d111810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d92538 q = 1) (hb : d111811 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d92538, d111811, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92538, d111811, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro17740 (p : Pattern) (ha : d92558 p = 1) (hb : d111819 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d92507 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d92513 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d92527 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d92484 q = 1) (hb : d111806 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d92484, d111806, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17545 q ha hb
    | true =>
      simp only [d92484, d111806, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro63 q hb ha
  have h4 (q : Pattern) (ha : d92528 q = 1) (hb : d111807 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d92528, d111807, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d92528, d111807, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d92534 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d92535 q = 1) (hb : d111808 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d92535, d111808, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d92535, d111808, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d92536 q = 1) (hb : d111809 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d92536, d111809, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d92536, d111809, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d92537 q = 1) (hb : d111810 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d92537, d111810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92537, d111810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d92543 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d92547 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d92550 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d92493 q = 1) (hb : d111814 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d92493, d111814, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17547 q ha hb
    | true =>
      simp only [d92493, d111814, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro66 q hb ha
  have h13 (q : Pattern) (ha : d92551 q = 1) (hb : d111815 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d92551, d111815, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
    | true =>
      simp only [d92551, d111815, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d92554 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d92555 q = 1) (hb : d111816 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d92555, d111816, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d92555, d111816, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d92556 q = 1) (hb : d111817 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d92556, d111817, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
    | true =>
      simp only [d92556, d111817, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d92557 q = 1) (hb : d111818 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d92557, d111818, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
    | true =>
      simp only [d92557, d111818, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d92558 q = 1) (hb : d111819 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d92558, d111819, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d92558, d111819, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro17741 (p : Pattern) (ha : d92572 p = 1) (hb : d112497 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d92550 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d92493 q = 1) (hb : d111814 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d92493, d111814, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17547 q ha hb
    | true =>
      simp only [d92493, d111814, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro66 q hb ha
  have h3 (q : Pattern) (ha : d92551 q = 1) (hb : d111815 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d92551, d111815, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d92551, d111815, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d92554 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d92555 q = 1) (hb : d111816 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d92555, d111816, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d92555, d111816, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d92570 q = 1) (hb : d111817 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d92570, d111817, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92570, d111817, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d92571 q = 1) (hb : d111818 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d92571, d111818, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92571, d111818, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d92572 q = 1) (hb : d112497 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d92572, d112497, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92572, d112497, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro17742 (p : Pattern) (ha : d92595 p = 1) (hb : d111786 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d92450 q = 1) (hb : d98879 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d92450, d98879, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17540 q ha hb
    | true =>
      simp only [d92450, d98879, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d92451 q = 1) (hb : d98880 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d92451, d98880, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92451, d98880, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d684 q = 1) (hb : d52388 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d684, d52388, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro71 q ha hb
    | true =>
      simp only [d684, d52388, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d685 q = 1) (hb : d52389 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d685, d52389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d685, d52389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d92592 q = 1) (hb : d111783 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d92592, d111783, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d92592, d111783, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d92593 q = 1) (hb : d111784 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d92593, d111784, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d92593, d111784, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d92594 q = 1) (hb : d111785 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d92594, d111785, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d92594, d111785, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d92595 q = 1) (hb : d111786 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d92595, d111786, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d92595, d111786, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro17743 (p : Pattern) (ha : d92607 p = 1) (hb : d112508 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d92591 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d92596 q = 1) (hb : d112503 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d92596, d112503, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17742 q ha hb
    | true =>
      simp only [d92596, d112503, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72 q hb ha
  have h3 (q : Pattern) (ha : d92597 q = 1) (hb : d112504 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d92597, d112504, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d92597, d112504, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d92603 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d92604 q = 1) (hb : d112505 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d92604, d112505, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d92604, d112505, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d92605 q = 1) (hb : d112506 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d92605, d112506, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92605, d112506, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d92606 q = 1) (hb : d112507 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d92606, d112507, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92606, d112507, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d92607 q = 1) (hb : d112508 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d92607, d112508, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92607, d112508, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro17744 (p : Pattern) (ha : d92613 p = 1) (hb : d112514 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d92501 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d92559 q = 1) (hb : d111820 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d92559, d111820, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17739 q ha hb
    | true =>
      simp only [d92559, d111820, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17740 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d92566 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d92567 q = 1) (hb : d111821 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d92567, d111821, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d92567, d111821, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d92568 q = 1) (hb : d112495 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d92568, d112495, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d92568, d112495, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d92569 q = 1) (hb : d112496 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d92569, d112496, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92569, d112496, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d92573 q = 1) (hb : d112498 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d92573, d112498, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d92573, d112498, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17741 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d52358 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d92574 q = 1) (hb : d112499 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d92574, d112499, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d92574, d112499, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d92575 q = 1) (hb : d112500 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d92575, d112500, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d92575, d112500, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h11 (q : Pattern) (ha : d92576 q = 1) (hb : d112501 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d92576, d112501, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d92576, d112501, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h12 (q : Pattern) (ha : d92577 q = 1) (hb : d112502 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d92577, d112502, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d92577, d112502, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d92608 q = 1) (hb : d112509 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d92608, d112509, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d92608, d112509, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17743 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d52414 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d92609 q = 1) (hb : d112510 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d92609, d112510, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d92609, d112510, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d92610 q = 1) (hb : d112511 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d92610, d112511, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d92610, d112511, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h17 (q : Pattern) (ha : d92611 q = 1) (hb : d112512 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d92611, d112512, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d92611, d112512, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h18 (q : Pattern) (ha : d92612 q = 1) (hb : d112513 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d92612, d112513, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d92612, d112513, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h19 (q : Pattern) (ha : d92613 q = 1) (hb : d112514 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d92613, d112514, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d92613, d112514, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro17745 (p : Pattern) (ha : d92619 p = 1) (hb : d112520 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d92614 q = 1) (hb : d112515 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d92614, d112515, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92614, d112515, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17744 q ha hb
  have h2 (q : Pattern) (ha : d92615 q = 1) (hb : d112516 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d92615, d112516, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92615, d112516, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d92616 q = 1) (hb : d112517 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d92616, d112517, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92616, d112517, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d92617 q = 1) (hb : d112518 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d92617, d112518, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92617, d112518, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d92618 q = 1) (hb : d112519 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d92618, d112519, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92618, d112519, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d92619 q = 1) (hb : d112520 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d92619, d112520, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92619, d112520, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro17746 (p : Pattern) (ha : d92683 p = 1) (hb : d111930 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d92652 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d92658 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d92672 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d92629 q = 1) (hb : d111925 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d92629, d111925, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17574 q ha hb
    | true =>
      simp only [d92629, d111925, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro107 q hb ha
  have h5 (q : Pattern) (ha : d92673 q = 1) (hb : d111926 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d92673, d111926, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d92673, d111926, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d92679 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d92680 q = 1) (hb : d111927 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d92680, d111927, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d92680, d111927, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d92681 q = 1) (hb : d111928 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d92681, d111928, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d92681, d111928, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d92682 q = 1) (hb : d111929 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d92682, d111929, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d92682, d111929, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d92683 q = 1) (hb : d111930 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d92683, d111930, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92683, d111930, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro17747 (p : Pattern) (ha : d92703 p = 1) (hb : d111939 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d92652 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d92658 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d92672 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d92629 q = 1) (hb : d111925 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d92629, d111925, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17574 q ha hb
    | true =>
      simp only [d92629, d111925, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro107 q hb ha
  have h4 (q : Pattern) (ha : d92673 q = 1) (hb : d111926 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d92673, d111926, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d92673, d111926, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d92679 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d92680 q = 1) (hb : d111927 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d92680, d111927, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d92680, d111927, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d92681 q = 1) (hb : d111928 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d92681, d111928, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d92681, d111928, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d92682 q = 1) (hb : d111929 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d92682, d111929, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92682, d111929, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d92688 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d92692 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d92695 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d92638 q = 1) (hb : d111934 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d92638, d111934, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17576 q ha hb
    | true =>
      simp only [d92638, d111934, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro110 q hb ha
  have h13 (q : Pattern) (ha : d92696 q = 1) (hb : d111935 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d92696, d111935, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
    | true =>
      simp only [d92696, d111935, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d92699 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d92700 q = 1) (hb : d111936 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d92700, d111936, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d92700, d111936, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d92701 q = 1) (hb : d111937 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d92701, d111937, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
    | true =>
      simp only [d92701, d111937, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d92702 q = 1) (hb : d111938 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d92702, d111938, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
    | true =>
      simp only [d92702, d111938, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d92703 q = 1) (hb : d111939 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d92703, d111939, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d92703, d111939, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro17748 (p : Pattern) (ha : d92717 p = 1) (hb : d112524 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d92695 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d92638 q = 1) (hb : d111934 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d92638, d111934, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17576 q ha hb
    | true =>
      simp only [d92638, d111934, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro110 q hb ha
  have h3 (q : Pattern) (ha : d92696 q = 1) (hb : d111935 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d92696, d111935, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d92696, d111935, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d92699 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d92700 q = 1) (hb : d111936 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d92700, d111936, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d92700, d111936, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d92715 q = 1) (hb : d111937 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d92715, d111937, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92715, d111937, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d92716 q = 1) (hb : d111938 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d92716, d111938, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92716, d111938, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d92717 q = 1) (hb : d112524 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d92717, d112524, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92717, d112524, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro17749 (p : Pattern) (ha : d92744 p = 1) (hb : d112019 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d92739 q = 1) (hb : d98939 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d92739, d98939, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17598 q ha hb
    | true =>
      simp only [d92739, d98939, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d92740 q = 1) (hb : d98940 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d92740, d98940, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92740, d98940, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d1006 q = 1) (hb : d52625 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d1006, d52625, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro117 q ha hb
    | true =>
      simp only [d1006, d52625, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d1007 q = 1) (hb : d52626 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d1007, d52626, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1007, d52626, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d92741 q = 1) (hb : d112016 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d92741, d112016, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d92741, d112016, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d92742 q = 1) (hb : d112017 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d92742, d112017, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d92742, d112017, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d92743 q = 1) (hb : d112018 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d92743, d112018, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d92743, d112018, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d92744 q = 1) (hb : d112019 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d92744, d112019, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d92744, d112019, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
end NetHack.Soko22Hazard87
