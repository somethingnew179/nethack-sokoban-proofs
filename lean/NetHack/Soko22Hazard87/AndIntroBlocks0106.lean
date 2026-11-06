import NetHack.Soko22Hazard87.AndIntroBlocks0105
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Soko22Hazard87
open NetHack.Sokoban NetHack.Sokoban.PatternCorrection
theorem andIntro26500 (p : Pattern) (ha : d11379 p = 1) (hb : d142666 p = 1) : d145647 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d142666 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d11369 q = 1) (hb : d142666 q = 1) : d145637 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d11369, d142666, d145637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26498 q ha hb
    | true =>
      simp only [d11369, d142666, d145637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d11370 q = 1) (hb : d142666 q = 1) : d145638 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d11370, d145638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11370, d145638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d11371 q = 1) (hb : d142666 q = 1) : d145639 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d11371, d145639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11371, d145639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d11373 q = 1) (hb : d142666 q = 1) : d145641 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d11373, d145641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d11373, d145641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d11378 q = 1) (hb : d142666 q = 1) : d145646 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d11378, d145646, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d11378, d145646, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d11379 q = 1) (hb : d142666 q = 1) : d145647 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d11379, d145647, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d11379, d145647, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h7 p ha hb
theorem andIntro26501 (p : Pattern) (ha : d11385 p = 1) (hb : d142666 p = 1) : d145653 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d142666 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d11376 q = 1) (hb : d142666 q = 1) : d145644 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d11376, d145644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26499 q ha hb
    | true =>
      simp only [d11376, d145644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d11377 q = 1) (hb : d142666 q = 1) : d145645 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d11377, d145645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11377, d145645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d11380 q = 1) (hb : d142666 q = 1) : d145648 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d11380, d145648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26500 q ha hb
    | true =>
      simp only [d11380, d145648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d11381 q = 1) (hb : d142666 q = 1) : d145649 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d11381, d145649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11381, d145649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d11382 q = 1) (hb : d142666 q = 1) : d145650 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d11382, d145650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d11382, d145650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d11383 q = 1) (hb : d142666 q = 1) : d145651 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d11383, d145651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d11383, d145651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d11384 q = 1) (hb : d142666 q = 1) : d145652 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d11384, d145652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d11384, d145652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d11385 q = 1) (hb : d142666 q = 1) : d145653 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d11385, d145653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11385, d145653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro26502 (p : Pattern) (ha : d11389 p = 1) (hb : d142666 p = 1) : d145657 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d142666 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d11380 q = 1) (hb : d142666 q = 1) : d145648 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d11380, d145648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26500 q ha hb
    | true =>
      simp only [d11380, d145648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d11381 q = 1) (hb : d142666 q = 1) : d145649 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d11381, d145649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11381, d145649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d11386 q = 1) (hb : d142666 q = 1) : d145654 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d11386, d145654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d11386, d145654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d11387 q = 1) (hb : d142666 q = 1) : d145655 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d11387, d145655, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d11387, d145655, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d11388 q = 1) (hb : d142666 q = 1) : d145656 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d11388, d145656, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d11388, d145656, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d11389 q = 1) (hb : d142666 q = 1) : d145657 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d11389, d145657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11389, d145657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro26503 (p : Pattern) (ha : d11395 p = 1) (hb : d142666 p = 1) : d145663 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d142666 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d11390 q = 1) (hb : d142666 q = 1) : d145658 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d11390, d145658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26501 q ha hb
    | true =>
      simp only [d11390, d145658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26502 q ha hb
  have h2 (q : Pattern) (ha : d11391 q = 1) (hb : d142666 q = 1) : d145659 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d11391, d145659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11391, d145659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d11392 q = 1) (hb : d142666 q = 1) : d145660 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d11392, d145660, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d11392, d145660, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d11393 q = 1) (hb : d142666 q = 1) : d145661 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d11393, d145661, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11393, d145661, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d11394 q = 1) (hb : d142666 q = 1) : d145662 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d11394, d145662, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11394, d145662, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d11395 q = 1) (hb : d142666 q = 1) : d145663 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d11395, d145663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11395, d145663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro26504 (p : Pattern) (ha : d11398 p = 1) (hb : d142666 p = 1) : d145666 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d142666 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d11376 q = 1) (hb : d142666 q = 1) : d145644 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d11376, d145644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26499 q ha hb
    | true =>
      simp only [d11376, d145644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d11377 q = 1) (hb : d142666 q = 1) : d145645 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d11377, d145645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11377, d145645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d11380 q = 1) (hb : d142666 q = 1) : d145648 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d11380, d145648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26500 q ha hb
    | true =>
      simp only [d11380, d145648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d11381 q = 1) (hb : d142666 q = 1) : d145649 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d11381, d145649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11381, d145649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d11382 q = 1) (hb : d142666 q = 1) : d145650 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d11382, d145650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d11382, d145650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d11383 q = 1) (hb : d142666 q = 1) : d145651 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d11383, d145651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d11383, d145651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d11384 q = 1) (hb : d142666 q = 1) : d145652 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d11384, d145652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d11384, d145652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d11398 q = 1) (hb : d142666 q = 1) : d145666 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d11398, d145666, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d11398, d145666, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro26505 (p : Pattern) (ha : d11399 p = 1) (hb : d142666 p = 1) : d145667 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d142666 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d11380 q = 1) (hb : d142666 q = 1) : d145648 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d11380, d145648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26500 q ha hb
    | true =>
      simp only [d11380, d145648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d11381 q = 1) (hb : d142666 q = 1) : d145649 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d11381, d145649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11381, d145649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d11386 q = 1) (hb : d142666 q = 1) : d145654 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d11386, d145654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d11386, d145654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d11387 q = 1) (hb : d142666 q = 1) : d145655 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d11387, d145655, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d11387, d145655, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d11388 q = 1) (hb : d142666 q = 1) : d145656 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d11388, d145656, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d11388, d145656, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d11399 q = 1) (hb : d142666 q = 1) : d145667 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d11399, d145667, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d11399, d145667, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro26506 (p : Pattern) (ha : d11405 p = 1) (hb : d142666 p = 1) : d145673 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d142666 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d11390 q = 1) (hb : d142666 q = 1) : d145658 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d11390, d145658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26501 q ha hb
    | true =>
      simp only [d11390, d145658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26502 q ha hb
  have h2 (q : Pattern) (ha : d11391 q = 1) (hb : d142666 q = 1) : d145659 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d11391, d145659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11391, d145659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d11392 q = 1) (hb : d142666 q = 1) : d145660 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d11392, d145660, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d11392, d145660, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d11393 q = 1) (hb : d142666 q = 1) : d145661 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d11393, d145661, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11393, d145661, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d11394 q = 1) (hb : d142666 q = 1) : d145662 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d11394, d145662, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11394, d145662, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d11400 q = 1) (hb : d142666 q = 1) : d145668 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d11400, d145668, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26504 q ha hb
    | true =>
      simp only [d11400, d145668, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26505 q ha hb
  have h7 (q : Pattern) (ha : d11401 q = 1) (hb : d142666 q = 1) : d145669 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d11401, d145669, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11401, d145669, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d11402 q = 1) (hb : d142666 q = 1) : d145670 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d11402, d145670, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d11402, d145670, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d11403 q = 1) (hb : d142666 q = 1) : d145671 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d11403, d145671, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11403, d145671, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d11404 q = 1) (hb : d142666 q = 1) : d145672 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d11404, d145672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11404, d145672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d11405 q = 1) (hb : d142666 q = 1) : d145673 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d11405, d145673, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d11405, d145673, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro26507 (p : Pattern) (ha : d11513 p = 1) (hb : d142666 p = 1) : d145755 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d142666 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d11390 q = 1) (hb : d142666 q = 1) : d145658 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d11390, d145658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26501 q ha hb
    | true =>
      simp only [d11390, d145658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26502 q ha hb
  have h2 (q : Pattern) (ha : d11391 q = 1) (hb : d142666 q = 1) : d145659 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d11391, d145659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11391, d145659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d11392 q = 1) (hb : d142666 q = 1) : d145660 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d11392, d145660, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d11392, d145660, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d11393 q = 1) (hb : d142666 q = 1) : d145661 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d11393, d145661, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11393, d145661, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d11394 q = 1) (hb : d142666 q = 1) : d145662 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d11394, d145662, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11394, d145662, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d11508 q = 1) (hb : d142666 q = 1) : d145750 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d11508, d145750, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26502 q ha hb
    | true =>
      simp only [d11508, d145750, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d11509 q = 1) (hb : d142666 q = 1) : d145751 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d11509, d145751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11509, d145751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d11510 q = 1) (hb : d142666 q = 1) : d145752 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d11510, d145752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d11510, d145752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d11511 q = 1) (hb : d142666 q = 1) : d145753 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d11511, d145753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11511, d145753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d11512 q = 1) (hb : d142666 q = 1) : d145754 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d11512, d145754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11512, d145754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d11513 q = 1) (hb : d142666 q = 1) : d145755 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d11513, d145755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d11513, d145755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro26508 (p : Pattern) (ha : d11519 p = 1) (hb : d142666 p = 1) : d145761 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d142666 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d11508 q = 1) (hb : d142666 q = 1) : d145750 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d11508, d145750, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26502 q ha hb
    | true =>
      simp only [d11508, d145750, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d11509 q = 1) (hb : d142666 q = 1) : d145751 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d11509, d145751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11509, d145751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d11510 q = 1) (hb : d142666 q = 1) : d145752 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d11510, d145752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d11510, d145752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d11511 q = 1) (hb : d142666 q = 1) : d145753 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d11511, d145753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11511, d145753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d11512 q = 1) (hb : d142666 q = 1) : d145754 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d11512, d145754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11512, d145754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d11514 q = 1) (hb : d142666 q = 1) : d145756 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d11514, d145756, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26505 q ha hb
    | true =>
      simp only [d11514, d145756, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d11515 q = 1) (hb : d142666 q = 1) : d145757 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d11515, d145757, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11515, d145757, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d11516 q = 1) (hb : d142666 q = 1) : d145758 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d11516, d145758, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d11516, d145758, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d11517 q = 1) (hb : d142666 q = 1) : d145759 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d11517, d145759, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11517, d145759, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d11518 q = 1) (hb : d142666 q = 1) : d145760 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d11518, d145760, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11518, d145760, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d11519 q = 1) (hb : d142666 q = 1) : d145761 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d11519, d145761, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d11519, d145761, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro26509 (p : Pattern) (ha : d11528 p = 1) (hb : d142666 p = 1) : d145770 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d142666 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d11514 q = 1) (hb : d142666 q = 1) : d145756 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d11514, d145756, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26505 q ha hb
    | true =>
      simp only [d11514, d145756, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d11515 q = 1) (hb : d142666 q = 1) : d145757 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d11515, d145757, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11515, d145757, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d11516 q = 1) (hb : d142666 q = 1) : d145758 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d11516, d145758, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d11516, d145758, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d11517 q = 1) (hb : d142666 q = 1) : d145759 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d11517, d145759, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11517, d145759, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d11518 q = 1) (hb : d142666 q = 1) : d145760 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d11518, d145760, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11518, d145760, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d11528 q = 1) (hb : d142666 q = 1) : d145770 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d11528, d145770, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11528, d145770, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro26510 (p : Pattern) (ha : d1401 p = 1) (hb : d142665 p = 1) : d145785 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1395 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1400 q = 1) (hb : d122304 q = 1) : d1400 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d1401 q = 1) (hb : d142665 q = 1) : d145785 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d1401, d142665, d145785, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d1401, d142665, d145785, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  exact h2 p ha hb
theorem andIntro26511 (p : Pattern) (ha : d11559 p = 1) (hb : d142666 p = 1) : d145804 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d142666 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d11541 q = 1) (hb : d142666 q = 1) : d145786 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d11541, d142666, d145786, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26510 q ha hb
    | true =>
      simp only [d11541, d142666, d145786, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d11542 q = 1) (hb : d142666 q = 1) : d145787 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d11542, d145787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11542, d145787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d11543 q = 1) (hb : d142666 q = 1) : d145788 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d11543, d145788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11543, d145788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d11549 q = 1) (hb : d142666 q = 1) : d145794 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d11549, d145794, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d11549, d145794, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d11558 q = 1) (hb : d142666 q = 1) : d145803 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d11558, d145803, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d11558, d145803, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d11559 q = 1) (hb : d142666 q = 1) : d145804 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d11559, d145804, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d11559, d145804, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h7 p ha hb
theorem andIntro26512 (p : Pattern) (ha : d11615 p = 1) (hb : d142666 p = 1) : d145836 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d142666 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d11560 q = 1) (hb : d142666 q = 1) : d145805 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d11560, d145805, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26511 q ha hb
    | true =>
      simp only [d11560, d145805, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d11561 q = 1) (hb : d142666 q = 1) : d145806 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d11561, d145806, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11561, d145806, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d11612 q = 1) (hb : d142666 q = 1) : d145833 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d11612, d145833, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d11612, d145833, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d11613 q = 1) (hb : d142666 q = 1) : d145834 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d11613, d145834, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d11613, d145834, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d11614 q = 1) (hb : d142666 q = 1) : d145835 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d11614, d145835, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d11614, d145835, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d11615 q = 1) (hb : d142666 q = 1) : d145836 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d11615, d145836, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d11615, d145836, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro26513 (p : Pattern) (ha : d11621 p = 1) (hb : d142666 p = 1) : d145842 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d142666 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d11616 q = 1) (hb : d142666 q = 1) : d145837 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d11616, d145837, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26512 q ha hb
    | true =>
      simp only [d11616, d145837, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d11617 q = 1) (hb : d142666 q = 1) : d145838 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d11617, d145838, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11617, d145838, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d11618 q = 1) (hb : d142666 q = 1) : d145839 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d11618, d145839, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d11618, d145839, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d11619 q = 1) (hb : d142666 q = 1) : d145840 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d11619, d145840, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11619, d145840, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d11620 q = 1) (hb : d142666 q = 1) : d145841 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d11620, d145841, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11620, d145841, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d11621 q = 1) (hb : d142666 q = 1) : d145842 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d11621, d145842, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11621, d145842, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro26514 (p : Pattern) (ha : d11410 p = 1) (hb : d142666 p = 1) : d145678 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d142666 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d11376 q = 1) (hb : d142666 q = 1) : d145644 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d11376, d145644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26499 q ha hb
    | true =>
      simp only [d11376, d145644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d11377 q = 1) (hb : d142666 q = 1) : d145645 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d11377, d145645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11377, d145645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d11380 q = 1) (hb : d142666 q = 1) : d145648 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d11380, d145648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26500 q ha hb
    | true =>
      simp only [d11380, d145648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d11381 q = 1) (hb : d142666 q = 1) : d145649 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d11381, d145649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11381, d145649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d11382 q = 1) (hb : d142666 q = 1) : d145650 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d11382, d145650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d11382, d145650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d11383 q = 1) (hb : d142666 q = 1) : d145651 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d11383, d145651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d11383, d145651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d11409 q = 1) (hb : d142666 q = 1) : d145677 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d11409, d145677, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11409, d145677, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d11410 q = 1) (hb : d142666 q = 1) : d145678 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d11410, d145678, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11410, d145678, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro26515 (p : Pattern) (ha : d11412 p = 1) (hb : d142666 p = 1) : d145680 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d142666 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d11380 q = 1) (hb : d142666 q = 1) : d145648 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d11380, d145648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26500 q ha hb
    | true =>
      simp only [d11380, d145648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d11381 q = 1) (hb : d142666 q = 1) : d145649 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d11381, d145649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11381, d145649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d11386 q = 1) (hb : d142666 q = 1) : d145654 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d11386, d145654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d11386, d145654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d11387 q = 1) (hb : d142666 q = 1) : d145655 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d11387, d145655, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d11387, d145655, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d11411 q = 1) (hb : d142666 q = 1) : d145679 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d11411, d145679, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11411, d145679, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d11412 q = 1) (hb : d142666 q = 1) : d145680 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d11412, d145680, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11412, d145680, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro26516 (p : Pattern) (ha : d11419 p = 1) (hb : d142666 p = 1) : d145687 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d142666 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d11376 q = 1) (hb : d142666 q = 1) : d145644 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d11376, d145644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26499 q ha hb
    | true =>
      simp only [d11376, d145644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d11377 q = 1) (hb : d142666 q = 1) : d145645 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d11377, d145645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11377, d145645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d11380 q = 1) (hb : d142666 q = 1) : d145648 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d11380, d145648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26500 q ha hb
    | true =>
      simp only [d11380, d145648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d11381 q = 1) (hb : d142666 q = 1) : d145649 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d11381, d145649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11381, d145649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d11382 q = 1) (hb : d142666 q = 1) : d145650 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d11382, d145650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d11382, d145650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d11417 q = 1) (hb : d142666 q = 1) : d145685 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d11417, d145685, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11417, d145685, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d11418 q = 1) (hb : d142666 q = 1) : d145686 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d11418, d145686, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d11418, d145686, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d11419 q = 1) (hb : d142666 q = 1) : d145687 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d11419, d145687, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11419, d145687, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro26517 (p : Pattern) (ha : d11422 p = 1) (hb : d142666 p = 1) : d145690 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d142666 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d11380 q = 1) (hb : d142666 q = 1) : d145648 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d11380, d145648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26500 q ha hb
    | true =>
      simp only [d11380, d145648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d11381 q = 1) (hb : d142666 q = 1) : d145649 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d11381, d145649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11381, d145649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d11386 q = 1) (hb : d142666 q = 1) : d145654 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d11386, d145654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d11386, d145654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d11420 q = 1) (hb : d142666 q = 1) : d145688 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d11420, d145688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11420, d145688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d11421 q = 1) (hb : d142666 q = 1) : d145689 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d11421, d145689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d11421, d145689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d11422 q = 1) (hb : d142666 q = 1) : d145690 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d11422, d145690, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11422, d145690, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro26518 (p : Pattern) (ha : d1215 p = 1) (hb : d142665 p = 1) : d145694 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1214 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1 q = 1) (hb : d1103 q = 1) : d1103 q = 1 := by
    exact hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d1113 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d1114 q = 1) (hb : d122304 q = 1) : d14757 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d1114, d122304, d14757, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d1114, d122304, d14757, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d1215 q = 1) (hb : d142665 q = 1) : d145694 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d1215, d142665, d145694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d1215, d142665, d145694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  exact h4 p ha hb
theorem andIntro26519 (p : Pattern) (ha : d11431 p = 1) (hb : d142666 p = 1) : d145700 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d142666 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d11426 q = 1) (hb : d142666 q = 1) : d145695 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d11426, d142666, d145695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26518 q ha hb
    | true =>
      simp only [d11426, d142666, d145695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d11427 q = 1) (hb : d142666 q = 1) : d145696 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d11427, d145696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11427, d145696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d11428 q = 1) (hb : d142666 q = 1) : d145697 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d11428, d145697, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11428, d145697, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d11366 q = 1) (hb : d142666 q = 1) : d145633 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d11366, d142666, d145633, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26497 q ha hb
    | true =>
      simp only [d11366, d142666, d145633, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h6 (q : Pattern) (ha : d11367 q = 1) (hb : d142666 q = 1) : d145634 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d11367, d145634, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11367, d145634, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d11368 q = 1) (hb : d142666 q = 1) : d145635 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d11368, d145635, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11368, d145635, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d11429 q = 1) (hb : d142666 q = 1) : d145698 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d11429, d145698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d11429, d145698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d11369 q = 1) (hb : d142666 q = 1) : d145637 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d11369, d142666, d145637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26498 q ha hb
    | true =>
      simp only [d11369, d142666, d145637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h10 (q : Pattern) (ha : d11370 q = 1) (hb : d142666 q = 1) : d145638 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d11370, d145638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11370, d145638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d11371 q = 1) (hb : d142666 q = 1) : d145639 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d11371, d145639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11371, d145639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d11372 q = 1) (hb : d142666 q = 1) : d145640 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d11372, d145640, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d11372, d145640, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d11430 q = 1) (hb : d142666 q = 1) : d145699 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d11430, d145699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d11430, d145699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d11431 q = 1) (hb : d142666 q = 1) : d145700 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d11431, d145700, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d11431, d145700, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h14 p ha hb
theorem andIntro26520 (p : Pattern) (ha : d11437 p = 1) (hb : d142666 p = 1) : d145706 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d142666 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d11432 q = 1) (hb : d142666 q = 1) : d145701 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d11432, d145701, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26519 q ha hb
    | true =>
      simp only [d11432, d145701, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d11433 q = 1) (hb : d142666 q = 1) : d145702 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d11433, d145702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11433, d145702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d11376 q = 1) (hb : d142666 q = 1) : d145644 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d11376, d145644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26499 q ha hb
    | true =>
      simp only [d11376, d145644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d11377 q = 1) (hb : d142666 q = 1) : d145645 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d11377, d145645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11377, d145645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d11434 q = 1) (hb : d142666 q = 1) : d145703 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d11434, d145703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d11434, d145703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d11435 q = 1) (hb : d142666 q = 1) : d145704 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d11435, d145704, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d11435, d145704, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d11436 q = 1) (hb : d142666 q = 1) : d145705 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d11436, d145705, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d11436, d145705, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d11437 q = 1) (hb : d142666 q = 1) : d145706 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d11437, d145706, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11437, d145706, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro26521 (p : Pattern) (ha : d5545 p = 1) (hb : d142665 p = 1) : d145709 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1125 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d5544 q = 1) (hb : d122304 q = 1) : d5544 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d5545 q = 1) (hb : d142665 q = 1) : d145709 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d5545, d142665, d145709, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d5545, d142665, d145709, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  exact h2 p ha hb
theorem andIntro26522 (p : Pattern) (ha : d11470 p = 1) (hb : d142666 p = 1) : d145715 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d142666 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d11366 q = 1) (hb : d142666 q = 1) : d145633 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d11366, d142666, d145633, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26497 q ha hb
    | true =>
      simp only [d11366, d142666, d145633, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d11367 q = 1) (hb : d142666 q = 1) : d145634 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d11367, d145634, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11367, d145634, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d11368 q = 1) (hb : d142666 q = 1) : d145635 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d11368, d145635, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11368, d145635, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d11369 q = 1) (hb : d142666 q = 1) : d145637 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d11369, d142666, d145637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26498 q ha hb
    | true =>
      simp only [d11369, d142666, d145637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h6 (q : Pattern) (ha : d11370 q = 1) (hb : d142666 q = 1) : d145638 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d11370, d145638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11370, d145638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d11371 q = 1) (hb : d142666 q = 1) : d145639 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d11371, d145639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11371, d145639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d11372 q = 1) (hb : d142666 q = 1) : d145640 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d11372, d145640, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d11372, d145640, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d11465 q = 1) (hb : d142666 q = 1) : d145710 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d11465, d142666, d145710, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26521 q ha hb
    | true =>
      simp only [d11465, d142666, d145710, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h10 (q : Pattern) (ha : d11466 q = 1) (hb : d142666 q = 1) : d145711 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d11466, d145711, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11466, d145711, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d11467 q = 1) (hb : d142666 q = 1) : d145712 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d11467, d145712, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11467, d145712, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d11468 q = 1) (hb : d142666 q = 1) : d145713 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d11468, d145713, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d11468, d145713, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d11469 q = 1) (hb : d142666 q = 1) : d145714 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d11469, d145714, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d11469, d145714, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d11470 q = 1) (hb : d142666 q = 1) : d145715 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d11470, d145715, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d11470, d145715, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h14 p ha hb
theorem andIntro26523 (p : Pattern) (ha : d11476 p = 1) (hb : d142666 p = 1) : d145721 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d142666 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d11471 q = 1) (hb : d142666 q = 1) : d145716 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d11471, d145716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26522 q ha hb
    | true =>
      simp only [d11471, d145716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d11472 q = 1) (hb : d142666 q = 1) : d145717 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d11472, d145717, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11472, d145717, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d11473 q = 1) (hb : d142666 q = 1) : d145718 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d11473, d145718, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d11473, d145718, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d11474 q = 1) (hb : d142666 q = 1) : d145719 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d11474, d145719, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d11474, d145719, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d11475 q = 1) (hb : d142666 q = 1) : d145720 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d11475, d145720, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d11475, d145720, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d11476 q = 1) (hb : d142666 q = 1) : d145721 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d11476, d145721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11476, d145721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro26524 (p : Pattern) (ha : d108942 p = 1) (hb : d142666 p = 1) : d145727 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d142666 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d11413 q = 1) (hb : d142666 q = 1) : d145681 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d11413, d145681, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26514 q ha hb
    | true =>
      simp only [d11413, d145681, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26515 q ha hb
  have h2 (q : Pattern) (ha : d11414 q = 1) (hb : d142666 q = 1) : d145682 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d11414, d145682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11414, d145682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d11415 q = 1) (hb : d142666 q = 1) : d145683 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d11415, d145683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d11415, d145683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d11416 q = 1) (hb : d142666 q = 1) : d145684 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d11416, d145684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11416, d145684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d11423 q = 1) (hb : d142666 q = 1) : d145691 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d11423, d145691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26516 q ha hb
    | true =>
      simp only [d11423, d145691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26517 q ha hb
  have h6 (q : Pattern) (ha : d11424 q = 1) (hb : d142666 q = 1) : d145692 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d11424, d145692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11424, d145692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d11425 q = 1) (hb : d142666 q = 1) : d145693 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d11425, d145693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d11425, d145693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d11438 q = 1) (hb : d142666 q = 1) : d145707 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d11438, d145707, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26520 q ha hb
    | true =>
      simp only [d11438, d145707, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26501 q ha hb
  have h9 (q : Pattern) (ha : d108938 q = 1) (hb : d142666 q = 1) : d145708 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d108938, d145708, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d108938, d145708, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d11477 q = 1) (hb : d142666 q = 1) : d145722 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d11477, d145722, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26523 q ha hb
    | true =>
      simp only [d11477, d145722, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d11478 q = 1) (hb : d142666 q = 1) : d145723 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d11478, d145723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d11478, d145723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d108939 q = 1) (hb : d142666 q = 1) : d145724 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d108939, d145724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d108939, d145724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d108940 q = 1) (hb : d142666 q = 1) : d145725 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d108940, d145725, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d108940, d145725, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d108941 q = 1) (hb : d142666 q = 1) : d145726 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d108941, d145726, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d108941, d145726, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d108942 q = 1) (hb : d142666 q = 1) : d145727 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d108942, d145727, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d108942, d145727, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro26525 (p : Pattern) (ha : d11483 p = 1) (hb : d142666 p = 1) : d145728 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d142666 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d11376 q = 1) (hb : d142666 q = 1) : d145644 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d11376, d145644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26499 q ha hb
    | true =>
      simp only [d11376, d145644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d11377 q = 1) (hb : d142666 q = 1) : d145645 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d11377, d145645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11377, d145645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d11380 q = 1) (hb : d142666 q = 1) : d145648 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d11380, d145648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26500 q ha hb
    | true =>
      simp only [d11380, d145648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d11381 q = 1) (hb : d142666 q = 1) : d145649 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d11381, d145649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11381, d145649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d11382 q = 1) (hb : d142666 q = 1) : d145650 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d11382, d145650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d11382, d145650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d11383 q = 1) (hb : d142666 q = 1) : d145651 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d11383, d145651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d11383, d145651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d11409 q = 1) (hb : d142666 q = 1) : d145677 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d11409, d145677, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11409, d145677, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d11483 q = 1) (hb : d142666 q = 1) : d145728 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d11483, d145728, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d11483, d145728, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro26526 (p : Pattern) (ha : d11484 p = 1) (hb : d142666 p = 1) : d145729 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d142666 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d11380 q = 1) (hb : d142666 q = 1) : d145648 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d11380, d145648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26500 q ha hb
    | true =>
      simp only [d11380, d145648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d11381 q = 1) (hb : d142666 q = 1) : d145649 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d11381, d145649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11381, d145649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d11386 q = 1) (hb : d142666 q = 1) : d145654 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d11386, d145654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d11386, d145654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d11387 q = 1) (hb : d142666 q = 1) : d145655 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d11387, d145655, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d11387, d145655, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d11411 q = 1) (hb : d142666 q = 1) : d145679 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d11411, d145679, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11411, d145679, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d11484 q = 1) (hb : d142666 q = 1) : d145729 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d11484, d145729, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d11484, d145729, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro26527 (p : Pattern) (ha : d11489 p = 1) (hb : d142666 p = 1) : d145734 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d142666 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d11376 q = 1) (hb : d142666 q = 1) : d145644 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d11376, d145644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26499 q ha hb
    | true =>
      simp only [d11376, d145644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d11377 q = 1) (hb : d142666 q = 1) : d145645 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d11377, d145645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11377, d145645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d11380 q = 1) (hb : d142666 q = 1) : d145648 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d11380, d145648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26500 q ha hb
    | true =>
      simp only [d11380, d145648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d11381 q = 1) (hb : d142666 q = 1) : d145649 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d11381, d145649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11381, d145649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d11382 q = 1) (hb : d142666 q = 1) : d145650 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d11382, d145650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d11382, d145650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d11417 q = 1) (hb : d142666 q = 1) : d145685 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d11417, d145685, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11417, d145685, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d11418 q = 1) (hb : d142666 q = 1) : d145686 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d11418, d145686, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d11418, d145686, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d11489 q = 1) (hb : d142666 q = 1) : d145734 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d11489, d145734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d11489, d145734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro26528 (p : Pattern) (ha : d11490 p = 1) (hb : d142666 p = 1) : d145735 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d142666 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d11380 q = 1) (hb : d142666 q = 1) : d145648 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d11380, d145648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26500 q ha hb
    | true =>
      simp only [d11380, d145648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d11381 q = 1) (hb : d142666 q = 1) : d145649 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d11381, d145649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11381, d145649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d11386 q = 1) (hb : d142666 q = 1) : d145654 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d11386, d145654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d11386, d145654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d11420 q = 1) (hb : d142666 q = 1) : d145688 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d11420, d145688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11420, d145688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d11421 q = 1) (hb : d142666 q = 1) : d145689 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d11421, d145689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d11421, d145689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d11490 q = 1) (hb : d142666 q = 1) : d145735 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d11490, d145735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d11490, d145735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro26529 (p : Pattern) (ha : d11494 p = 1) (hb : d142666 p = 1) : d145739 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d142666 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d11432 q = 1) (hb : d142666 q = 1) : d145701 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d11432, d145701, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26519 q ha hb
    | true =>
      simp only [d11432, d145701, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d11433 q = 1) (hb : d142666 q = 1) : d145702 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d11433, d145702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11433, d145702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d11376 q = 1) (hb : d142666 q = 1) : d145644 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d11376, d145644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26499 q ha hb
    | true =>
      simp only [d11376, d145644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d11377 q = 1) (hb : d142666 q = 1) : d145645 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d11377, d145645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11377, d145645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d11434 q = 1) (hb : d142666 q = 1) : d145703 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d11434, d145703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d11434, d145703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d11435 q = 1) (hb : d142666 q = 1) : d145704 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d11435, d145704, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d11435, d145704, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d11436 q = 1) (hb : d142666 q = 1) : d145705 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d11436, d145705, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d11436, d145705, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d11494 q = 1) (hb : d142666 q = 1) : d145739 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d11494, d145739, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d11494, d145739, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro26530 (p : Pattern) (ha : d11500 p = 1) (hb : d142666 p = 1) : d145742 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d142666 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d11471 q = 1) (hb : d142666 q = 1) : d145716 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d11471, d145716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26522 q ha hb
    | true =>
      simp only [d11471, d145716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d11472 q = 1) (hb : d142666 q = 1) : d145717 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d11472, d145717, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11472, d145717, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d11473 q = 1) (hb : d142666 q = 1) : d145718 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d11473, d145718, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d11473, d145718, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d11474 q = 1) (hb : d142666 q = 1) : d145719 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d11474, d145719, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d11474, d145719, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d11475 q = 1) (hb : d142666 q = 1) : d145720 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d11475, d145720, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d11475, d145720, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d11500 q = 1) (hb : d142666 q = 1) : d145742 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d11500, d145742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d11500, d145742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro26531 (p : Pattern) (ha : d108947 p = 1) (hb : d142666 p = 1) : d145748 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d142666 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d11413 q = 1) (hb : d142666 q = 1) : d145681 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d11413, d145681, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26514 q ha hb
    | true =>
      simp only [d11413, d145681, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26515 q ha hb
  have h2 (q : Pattern) (ha : d11414 q = 1) (hb : d142666 q = 1) : d145682 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d11414, d145682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11414, d145682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d11415 q = 1) (hb : d142666 q = 1) : d145683 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d11415, d145683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d11415, d145683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d11416 q = 1) (hb : d142666 q = 1) : d145684 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d11416, d145684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11416, d145684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d11423 q = 1) (hb : d142666 q = 1) : d145691 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d11423, d145691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26516 q ha hb
    | true =>
      simp only [d11423, d145691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26517 q ha hb
  have h6 (q : Pattern) (ha : d11424 q = 1) (hb : d142666 q = 1) : d145692 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d11424, d145692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11424, d145692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d11425 q = 1) (hb : d142666 q = 1) : d145693 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d11425, d145693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d11425, d145693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d11438 q = 1) (hb : d142666 q = 1) : d145707 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d11438, d145707, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26520 q ha hb
    | true =>
      simp only [d11438, d145707, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26501 q ha hb
  have h9 (q : Pattern) (ha : d108938 q = 1) (hb : d142666 q = 1) : d145708 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d108938, d145708, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d108938, d145708, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d11477 q = 1) (hb : d142666 q = 1) : d145722 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d11477, d145722, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26523 q ha hb
    | true =>
      simp only [d11477, d145722, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d11478 q = 1) (hb : d142666 q = 1) : d145723 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d11478, d145723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d11478, d145723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d108939 q = 1) (hb : d142666 q = 1) : d145724 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d108939, d145724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d108939, d145724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d108940 q = 1) (hb : d142666 q = 1) : d145725 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d108940, d145725, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d108940, d145725, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d108941 q = 1) (hb : d142666 q = 1) : d145726 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d108941, d145726, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d108941, d145726, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d11485 q = 1) (hb : d142666 q = 1) : d145730 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d11485, d145730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26525 q ha hb
    | true =>
      simp only [d11485, d145730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26526 q ha hb
  have h16 (q : Pattern) (ha : d11486 q = 1) (hb : d142666 q = 1) : d145731 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d11486, d145731, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11486, d145731, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d11487 q = 1) (hb : d142666 q = 1) : d145732 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d11487, d145732, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d11487, d145732, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h18 (q : Pattern) (ha : d11488 q = 1) (hb : d142666 q = 1) : d145733 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d11488, d145733, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11488, d145733, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d11491 q = 1) (hb : d142666 q = 1) : d145736 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d11491, d145736, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26527 q ha hb
    | true =>
      simp only [d11491, d145736, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26528 q ha hb
  have h20 (q : Pattern) (ha : d11492 q = 1) (hb : d142666 q = 1) : d145737 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d11492, d145737, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11492, d145737, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
  have h21 (q : Pattern) (ha : d11493 q = 1) (hb : d142666 q = 1) : d145738 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d11493, d145738, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d11493, d145738, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h22 (q : Pattern) (ha : d11495 q = 1) (hb : d142666 q = 1) : d145740 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d11495, d145740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26529 q ha hb
    | true =>
      simp only [d11495, d145740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26504 q ha hb
  have h23 (q : Pattern) (ha : d108943 q = 1) (hb : d142666 q = 1) : d145741 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d108943, d145741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
    | true =>
      simp only [d108943, d145741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h24 (q : Pattern) (ha : d11501 q = 1) (hb : d142666 q = 1) : d145743 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d11501, d145743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26530 q ha hb
    | true =>
      simp only [d11501, d145743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h25 (q : Pattern) (ha : d11502 q = 1) (hb : d142666 q = 1) : d145744 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d11502, d145744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q ha hb
    | true =>
      simp only [d11502, d145744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h26 (q : Pattern) (ha : d108944 q = 1) (hb : d142666 q = 1) : d145745 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d108944, d145745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
    | true =>
      simp only [d108944, d145745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q ha hb
  have h27 (q : Pattern) (ha : d108945 q = 1) (hb : d142666 q = 1) : d145746 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d108945, d145746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d108945, d145746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h26 q ha hb
  have h28 (q : Pattern) (ha : d108946 q = 1) (hb : d142666 q = 1) : d145747 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d108946, d145747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d108946, d145747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h27 q ha hb
  have h29 (q : Pattern) (ha : d108947 q = 1) (hb : d142666 q = 1) : d145748 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d108947, d145748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d108947, d145748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h28 q ha hb
  exact h29 p ha hb
theorem andIntro26532 (p : Pattern) (ha : d108954 p = 1) (hb : d142666 p = 1) : d145768 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d142666 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d11495 q = 1) (hb : d142666 q = 1) : d145740 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d11495, d145740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26529 q ha hb
    | true =>
      simp only [d11495, d145740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26504 q ha hb
  have h2 (q : Pattern) (ha : d108943 q = 1) (hb : d142666 q = 1) : d145741 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d108943, d145741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d108943, d145741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d11501 q = 1) (hb : d142666 q = 1) : d145743 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d11501, d145743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26530 q ha hb
    | true =>
      simp only [d11501, d145743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d11502 q = 1) (hb : d142666 q = 1) : d145744 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d11502, d145744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d11502, d145744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d108944 q = 1) (hb : d142666 q = 1) : d145745 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d108944, d145745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d108944, d145745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d108952 q = 1) (hb : d142666 q = 1) : d145766 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d108952, d145766, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d108952, d145766, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d108953 q = 1) (hb : d142666 q = 1) : d145767 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d108953, d145767, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d108953, d145767, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d108954 q = 1) (hb : d142666 q = 1) : d145768 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d108954, d145768, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d108954, d145768, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro26533 (p : Pattern) (ha : d1390 p = 1) (hb : d142665 p = 1) : d145776 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1384 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1 q = 1) (hb : d1383 q = 1) : d1383 q = 1 := by
    exact hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d1388 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d1389 q = 1) (hb : d122304 q = 1) : d14993 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d1389, d122304, d14993, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d1389, d122304, d14993, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d1390 q = 1) (hb : d142665 q = 1) : d145776 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d1390, d142665, d145776, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d1390, d142665, d145776, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  exact h4 p ha hb
theorem andIntro26534 (p : Pattern) (ha : d1396 p = 1) (hb : d142665 p = 1) : d145780 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1389 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1 q = 1) (hb : d1388 q = 1) : d1388 q = 1 := by
    exact hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d1394 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d1395 q = 1) (hb : d122304 q = 1) : d15014 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d1395, d122304, d15014, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d1395, d122304, d15014, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d1396 q = 1) (hb : d142665 q = 1) : d145780 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d1396, d142665, d145780, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d1396, d142665, d145780, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  exact h4 p ha hb
theorem andIntro26535 (p : Pattern) (ha : d11546 p = 1) (hb : d142666 p = 1) : d145791 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d142666 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d11534 q = 1) (hb : d142666 q = 1) : d145777 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d11534, d142666, d145777, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26533 q ha hb
    | true =>
      simp only [d11534, d142666, d145777, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d11535 q = 1) (hb : d142666 q = 1) : d145778 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d11535, d145778, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11535, d145778, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d11536 q = 1) (hb : d142666 q = 1) : d145779 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d11536, d145779, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11536, d145779, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d11537 q = 1) (hb : d142666 q = 1) : d145781 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d11537, d142666, d145781, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26534 q ha hb
    | true =>
      simp only [d11537, d142666, d145781, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h6 (q : Pattern) (ha : d11538 q = 1) (hb : d142666 q = 1) : d145782 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d11538, d145782, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11538, d145782, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d11539 q = 1) (hb : d142666 q = 1) : d145783 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d11539, d145783, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11539, d145783, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d11540 q = 1) (hb : d142666 q = 1) : d145784 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d11540, d145784, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d11540, d145784, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d11541 q = 1) (hb : d142666 q = 1) : d145786 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d11541, d142666, d145786, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26510 q ha hb
    | true =>
      simp only [d11541, d142666, d145786, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h10 (q : Pattern) (ha : d11542 q = 1) (hb : d142666 q = 1) : d145787 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d11542, d145787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11542, d145787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d11543 q = 1) (hb : d142666 q = 1) : d145788 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d11543, d145788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11543, d145788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d11544 q = 1) (hb : d142666 q = 1) : d145789 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d11544, d145789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d11544, d145789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d11545 q = 1) (hb : d142666 q = 1) : d145790 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d11545, d145790, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d11545, d145790, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d11546 q = 1) (hb : d142666 q = 1) : d145791 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d11546, d145791, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d11546, d145791, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h14 p ha hb
theorem andIntro26536 (p : Pattern) (ha : d11551 p = 1) (hb : d142666 p = 1) : d145796 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d142666 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d11537 q = 1) (hb : d142666 q = 1) : d145781 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d11537, d142666, d145781, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26534 q ha hb
    | true =>
      simp only [d11537, d142666, d145781, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d11538 q = 1) (hb : d142666 q = 1) : d145782 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d11538, d145782, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11538, d145782, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d11539 q = 1) (hb : d142666 q = 1) : d145783 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d11539, d145783, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11539, d145783, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d11541 q = 1) (hb : d142666 q = 1) : d145786 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d11541, d142666, d145786, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26510 q ha hb
    | true =>
      simp only [d11541, d142666, d145786, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h6 (q : Pattern) (ha : d11542 q = 1) (hb : d142666 q = 1) : d145787 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d11542, d145787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11542, d145787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d11543 q = 1) (hb : d142666 q = 1) : d145788 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d11543, d145788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11543, d145788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d11544 q = 1) (hb : d142666 q = 1) : d145789 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d11544, d145789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d11544, d145789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d11549 q = 1) (hb : d142666 q = 1) : d145794 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d11549, d145794, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d11549, d145794, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d11550 q = 1) (hb : d142666 q = 1) : d145795 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d11550, d145795, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d11550, d145795, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d11551 q = 1) (hb : d142666 q = 1) : d145796 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d11551, d145796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d11551, d145796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h11 p ha hb
theorem andIntro26537 (p : Pattern) (ha : d11557 p = 1) (hb : d142666 p = 1) : d145802 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d142666 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d11547 q = 1) (hb : d142666 q = 1) : d145792 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d11547, d145792, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26535 q ha hb
    | true =>
      simp only [d11547, d145792, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d11548 q = 1) (hb : d142666 q = 1) : d145793 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d11548, d145793, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11548, d145793, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d11552 q = 1) (hb : d142666 q = 1) : d145797 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d11552, d145797, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26536 q ha hb
    | true =>
      simp only [d11552, d145797, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d11553 q = 1) (hb : d142666 q = 1) : d145798 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d11553, d145798, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11553, d145798, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d11554 q = 1) (hb : d142666 q = 1) : d145799 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d11554, d145799, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d11554, d145799, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d11555 q = 1) (hb : d142666 q = 1) : d145800 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d11555, d145800, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d11555, d145800, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d11556 q = 1) (hb : d142666 q = 1) : d145801 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d11556, d145801, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d11556, d145801, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d11557 q = 1) (hb : d142666 q = 1) : d145802 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d11557, d145802, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d11557, d145802, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro26538 (p : Pattern) (ha : d11565 p = 1) (hb : d142666 p = 1) : d145810 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d142666 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d11552 q = 1) (hb : d142666 q = 1) : d145797 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d11552, d145797, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26536 q ha hb
    | true =>
      simp only [d11552, d145797, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d11553 q = 1) (hb : d142666 q = 1) : d145798 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d11553, d145798, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11553, d145798, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d11560 q = 1) (hb : d142666 q = 1) : d145805 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d11560, d145805, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26511 q ha hb
    | true =>
      simp only [d11560, d145805, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d11561 q = 1) (hb : d142666 q = 1) : d145806 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d11561, d145806, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11561, d145806, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d11562 q = 1) (hb : d142666 q = 1) : d145807 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d11562, d145807, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d11562, d145807, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d11563 q = 1) (hb : d142666 q = 1) : d145808 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d11563, d145808, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d11563, d145808, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d11564 q = 1) (hb : d142666 q = 1) : d145809 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d11564, d145809, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d11564, d145809, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d11565 q = 1) (hb : d142666 q = 1) : d145810 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d11565, d145810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d11565, d145810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro26539 (p : Pattern) (ha : d5589 p = 1) (hb : d142665 p = 1) : d145813 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1395 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d5588 q = 1) (hb : d122304 q = 1) : d5588 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d5589 q = 1) (hb : d142665 q = 1) : d145813 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d5589, d142665, d145813, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d5589, d142665, d145813, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  exact h2 p ha hb
theorem andIntro26540 (p : Pattern) (ha : d11598 p = 1) (hb : d142666 p = 1) : d145819 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d142666 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d11537 q = 1) (hb : d142666 q = 1) : d145781 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d11537, d142666, d145781, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26534 q ha hb
    | true =>
      simp only [d11537, d142666, d145781, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d11538 q = 1) (hb : d142666 q = 1) : d145782 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d11538, d145782, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11538, d145782, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d11539 q = 1) (hb : d142666 q = 1) : d145783 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d11539, d145783, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11539, d145783, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d11541 q = 1) (hb : d142666 q = 1) : d145786 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d11541, d142666, d145786, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26510 q ha hb
    | true =>
      simp only [d11541, d142666, d145786, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h6 (q : Pattern) (ha : d11542 q = 1) (hb : d142666 q = 1) : d145787 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d11542, d145787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11542, d145787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d11543 q = 1) (hb : d142666 q = 1) : d145788 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d11543, d145788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11543, d145788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d11544 q = 1) (hb : d142666 q = 1) : d145789 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d11544, d145789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d11544, d145789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d11593 q = 1) (hb : d142666 q = 1) : d145814 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d11593, d142666, d145814, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26539 q ha hb
    | true =>
      simp only [d11593, d142666, d145814, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h10 (q : Pattern) (ha : d11594 q = 1) (hb : d142666 q = 1) : d145815 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d11594, d145815, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11594, d145815, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d11595 q = 1) (hb : d142666 q = 1) : d145816 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d11595, d145816, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11595, d145816, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d11596 q = 1) (hb : d142666 q = 1) : d145817 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d11596, d145817, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d11596, d145817, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d11597 q = 1) (hb : d142666 q = 1) : d145818 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d11597, d145818, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d11597, d145818, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d11598 q = 1) (hb : d142666 q = 1) : d145819 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d11598, d145819, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d11598, d145819, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h14 p ha hb
theorem andIntro26541 (p : Pattern) (ha : d11604 p = 1) (hb : d142666 p = 1) : d145825 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d142666 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d11599 q = 1) (hb : d142666 q = 1) : d145820 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d11599, d145820, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26540 q ha hb
    | true =>
      simp only [d11599, d145820, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d11600 q = 1) (hb : d142666 q = 1) : d145821 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d11600, d145821, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11600, d145821, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d11601 q = 1) (hb : d142666 q = 1) : d145822 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d11601, d145822, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d11601, d145822, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d11602 q = 1) (hb : d142666 q = 1) : d145823 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d11602, d145823, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d11602, d145823, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d11603 q = 1) (hb : d142666 q = 1) : d145824 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d11603, d145824, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d11603, d145824, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d11604 q = 1) (hb : d142666 q = 1) : d145825 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d11604, d145825, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d11604, d145825, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro26542 (p : Pattern) (ha : d108964 p = 1) (hb : d142666 p = 1) : d145831 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d142666 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d11566 q = 1) (hb : d142666 q = 1) : d145811 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d11566, d145811, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26537 q ha hb
    | true =>
      simp only [d11566, d145811, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26538 q ha hb
  have h2 (q : Pattern) (ha : d108960 q = 1) (hb : d142666 q = 1) : d145812 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d108960, d145812, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d108960, d145812, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d11605 q = 1) (hb : d142666 q = 1) : d145826 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d11605, d145826, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26541 q ha hb
    | true =>
      simp only [d11605, d145826, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d11606 q = 1) (hb : d142666 q = 1) : d145827 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d11606, d145827, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d11606, d145827, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d108961 q = 1) (hb : d142666 q = 1) : d145828 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d108961, d145828, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d108961, d145828, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d108962 q = 1) (hb : d142666 q = 1) : d145829 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d108962, d145829, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d108962, d145829, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d108963 q = 1) (hb : d142666 q = 1) : d145830 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d108963, d145830, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d108963, d145830, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d108964 q = 1) (hb : d142666 q = 1) : d145831 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d108964, d145831, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d108964, d145831, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro26543 (p : Pattern) (ha : d108970 p = 1) (hb : d142666 p = 1) : d145848 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d142666 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d11396 q = 1) (hb : d142666 q = 1) : d145664 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d11396, d145664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11396, d145664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26503 q ha hb
  have h2 (q : Pattern) (ha : d11397 q = 1) (hb : d142666 q = 1) : d145665 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d11397, d145665, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d11397, d145665, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d11406 q = 1) (hb : d142666 q = 1) : d145674 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d11406, d145674, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26503 q ha hb
    | true =>
      simp only [d11406, d145674, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26506 q ha hb
  have h4 (q : Pattern) (ha : d11407 q = 1) (hb : d142666 q = 1) : d145675 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d11407, d145675, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d11407, d145675, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d11408 q = 1) (hb : d142666 q = 1) : d145676 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d11408, d145676, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d11408, d145676, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d108948 q = 1) (hb : d142666 q = 1) : d145749 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d108948, d145749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26524 q ha hb
    | true =>
      simp only [d108948, d145749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26531 q ha hb
  have h7 (q : Pattern) (ha : d11520 q = 1) (hb : d142666 q = 1) : d145762 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d11520, d145762, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26507 q ha hb
    | true =>
      simp only [d11520, d145762, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26508 q ha hb
  have h8 (q : Pattern) (ha : d108949 q = 1) (hb : d142666 q = 1) : d145763 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d108949, d145763, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d108949, d145763, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d108950 q = 1) (hb : d142666 q = 1) : d145764 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d108950, d145764, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d108950, d145764, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d108951 q = 1) (hb : d142666 q = 1) : d145765 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d108951, d145765, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d108951, d145765, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d108955 q = 1) (hb : d142666 q = 1) : d145769 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d108955, d145769, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d108955, d145769, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26532 q ha hb
  have h12 (q : Pattern) (ha : d11529 q = 1) (hb : d142666 q = 1) : d145771 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d11529, d145771, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11529, d145771, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26509 q ha hb
  have h13 (q : Pattern) (ha : d108956 q = 1) (hb : d142666 q = 1) : d145772 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d108956, d145772, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d108956, d145772, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d108957 q = 1) (hb : d142666 q = 1) : d145773 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d108957, d145773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d108957, d145773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d108958 q = 1) (hb : d142666 q = 1) : d145774 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d108958, d145774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d108958, d145774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h16 (q : Pattern) (ha : d108959 q = 1) (hb : d142666 q = 1) : d145775 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d108959, d145775, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d108959, d145775, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d108965 q = 1) (hb : d142666 q = 1) : d145832 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d108965, d145832, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d108965, d145832, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26542 q ha hb
  have h18 (q : Pattern) (ha : d11622 q = 1) (hb : d142666 q = 1) : d145843 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d11622, d145843, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11622, d145843, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26513 q ha hb
  have h19 (q : Pattern) (ha : d108966 q = 1) (hb : d142666 q = 1) : d145844 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d108966, d145844, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d108966, d145844, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d108967 q = 1) (hb : d142666 q = 1) : d145845 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d108967, d145845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d108967, d145845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h21 (q : Pattern) (ha : d108968 q = 1) (hb : d142666 q = 1) : d145846 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d108968, d145846, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d108968, d145846, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h22 (q : Pattern) (ha : d108969 q = 1) (hb : d142666 q = 1) : d145847 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d108969, d145847, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d108969, d145847, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h23 (q : Pattern) (ha : d108970 q = 1) (hb : d142666 q = 1) : d145848 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d108970, d145848, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d108970, d145848, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
  exact h23 p ha hb
theorem andIntro26544 (p : Pattern) (ha : d108976 p = 1) (hb : d142666 p = 1) : d145854 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d142666 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d108971 q = 1) (hb : d142666 q = 1) : d145849 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d108971, d145849, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d108971, d145849, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26543 q ha hb
  have h2 (q : Pattern) (ha : d108972 q = 1) (hb : d142666 q = 1) : d145850 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d108972, d145850, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d108972, d145850, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d108973 q = 1) (hb : d142666 q = 1) : d145851 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d108973, d145851, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d108973, d145851, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d108974 q = 1) (hb : d142666 q = 1) : d145852 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d108974, d145852, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d108974, d145852, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d108975 q = 1) (hb : d142666 q = 1) : d145853 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d108975, d145853, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d108975, d145853, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d108976 q = 1) (hb : d142666 q = 1) : d145854 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d108976, d145854, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d108976, d145854, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro26545 (p : Pattern) (ha : d1587 p = 1) (hb : d142665 p = 1) : d145858 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1574 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1 q = 1) (hb : d1573 q = 1) : d1573 q = 1 := by
    exact hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d1585 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d1586 q = 1) (hb : d122304 q = 1) : d15155 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d1586, d122304, d15155, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d1586, d122304, d15155, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d1587 q = 1) (hb : d142665 q = 1) : d145858 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d1587, d142665, d145858, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d1587, d142665, d145858, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  exact h4 p ha hb
theorem andIntro26546 (p : Pattern) (ha : d1589 p = 1) (hb : d142665 p = 1) : d145862 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1586 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1588 q = 1) (hb : d122304 q = 1) : d1588 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d1589 q = 1) (hb : d142665 q = 1) : d145862 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d1589, d142665, d145862, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d1589, d142665, d145862, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  exact h2 p ha hb
theorem andIntro26547 (p : Pattern) (ha : d11646 p = 1) (hb : d142666 p = 1) : d145869 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d142666 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d11637 q = 1) (hb : d142666 q = 1) : d145859 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d11637, d142666, d145859, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26545 q ha hb
    | true =>
      simp only [d11637, d142666, d145859, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d11638 q = 1) (hb : d142666 q = 1) : d145860 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d11638, d145860, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11638, d145860, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d11639 q = 1) (hb : d142666 q = 1) : d145861 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d11639, d145861, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11639, d145861, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d11640 q = 1) (hb : d142666 q = 1) : d145863 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d11640, d142666, d145863, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26546 q ha hb
    | true =>
      simp only [d11640, d142666, d145863, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h6 (q : Pattern) (ha : d11641 q = 1) (hb : d142666 q = 1) : d145864 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d11641, d145864, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11641, d145864, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d11642 q = 1) (hb : d142666 q = 1) : d145865 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d11642, d145865, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11642, d145865, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d11643 q = 1) (hb : d142666 q = 1) : d145866 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d11643, d145866, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d11643, d145866, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d11644 q = 1) (hb : d142666 q = 1) : d145867 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d11644, d145867, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d11644, d145867, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d11645 q = 1) (hb : d142666 q = 1) : d145868 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d11645, d145868, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d11645, d145868, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d11646 q = 1) (hb : d142666 q = 1) : d145869 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d11646, d145869, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d11646, d145869, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h11 p ha hb
theorem andIntro26548 (p : Pattern) (ha : d11650 p = 1) (hb : d142666 p = 1) : d145873 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d142666 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d11640 q = 1) (hb : d142666 q = 1) : d145863 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d11640, d142666, d145863, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26546 q ha hb
    | true =>
      simp only [d11640, d142666, d145863, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d11641 q = 1) (hb : d142666 q = 1) : d145864 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d11641, d145864, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11641, d145864, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d11642 q = 1) (hb : d142666 q = 1) : d145865 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d11642, d145865, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11642, d145865, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d11644 q = 1) (hb : d142666 q = 1) : d145867 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d11644, d145867, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d11644, d145867, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d11649 q = 1) (hb : d142666 q = 1) : d145872 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d11649, d145872, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d11649, d145872, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d11650 q = 1) (hb : d142666 q = 1) : d145873 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d11650, d145873, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d11650, d145873, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h7 p ha hb
theorem andIntro26549 (p : Pattern) (ha : d11656 p = 1) (hb : d142666 p = 1) : d145879 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d142666 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d11647 q = 1) (hb : d142666 q = 1) : d145870 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d11647, d145870, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26547 q ha hb
    | true =>
      simp only [d11647, d145870, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d11648 q = 1) (hb : d142666 q = 1) : d145871 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d11648, d145871, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11648, d145871, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d11651 q = 1) (hb : d142666 q = 1) : d145874 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d11651, d145874, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26548 q ha hb
    | true =>
      simp only [d11651, d145874, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d11652 q = 1) (hb : d142666 q = 1) : d145875 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d11652, d145875, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11652, d145875, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d11653 q = 1) (hb : d142666 q = 1) : d145876 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d11653, d145876, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d11653, d145876, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d11654 q = 1) (hb : d142666 q = 1) : d145877 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d11654, d145877, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d11654, d145877, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d11655 q = 1) (hb : d142666 q = 1) : d145878 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d11655, d145878, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d11655, d145878, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d11656 q = 1) (hb : d142666 q = 1) : d145879 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d11656, d145879, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11656, d145879, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro26550 (p : Pattern) (ha : d11660 p = 1) (hb : d142666 p = 1) : d145883 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d142666 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d11651 q = 1) (hb : d142666 q = 1) : d145874 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d11651, d145874, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26548 q ha hb
    | true =>
      simp only [d11651, d145874, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d11652 q = 1) (hb : d142666 q = 1) : d145875 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d11652, d145875, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11652, d145875, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d11657 q = 1) (hb : d142666 q = 1) : d145880 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d11657, d145880, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d11657, d145880, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d11658 q = 1) (hb : d142666 q = 1) : d145881 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d11658, d145881, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d11658, d145881, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d11659 q = 1) (hb : d142666 q = 1) : d145882 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d11659, d145882, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d11659, d145882, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d11660 q = 1) (hb : d142666 q = 1) : d145883 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d11660, d145883, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11660, d145883, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro26551 (p : Pattern) (ha : d11666 p = 1) (hb : d142666 p = 1) : d145889 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d142666 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d11661 q = 1) (hb : d142666 q = 1) : d145884 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d11661, d145884, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26549 q ha hb
    | true =>
      simp only [d11661, d145884, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26550 q ha hb
  have h2 (q : Pattern) (ha : d11662 q = 1) (hb : d142666 q = 1) : d145885 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d11662, d145885, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11662, d145885, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d11663 q = 1) (hb : d142666 q = 1) : d145886 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d11663, d145886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d11663, d145886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d11664 q = 1) (hb : d142666 q = 1) : d145887 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d11664, d145887, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11664, d145887, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d11665 q = 1) (hb : d142666 q = 1) : d145888 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d11665, d145888, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11665, d145888, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d11666 q = 1) (hb : d142666 q = 1) : d145889 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d11666, d145889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11666, d145889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro26552 (p : Pattern) (ha : d11669 p = 1) (hb : d142666 p = 1) : d145892 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d142666 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d11647 q = 1) (hb : d142666 q = 1) : d145870 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d11647, d145870, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26547 q ha hb
    | true =>
      simp only [d11647, d145870, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d11648 q = 1) (hb : d142666 q = 1) : d145871 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d11648, d145871, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11648, d145871, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d11651 q = 1) (hb : d142666 q = 1) : d145874 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d11651, d145874, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26548 q ha hb
    | true =>
      simp only [d11651, d145874, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d11652 q = 1) (hb : d142666 q = 1) : d145875 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d11652, d145875, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11652, d145875, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d11653 q = 1) (hb : d142666 q = 1) : d145876 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d11653, d145876, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d11653, d145876, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d11654 q = 1) (hb : d142666 q = 1) : d145877 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d11654, d145877, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d11654, d145877, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d11655 q = 1) (hb : d142666 q = 1) : d145878 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d11655, d145878, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d11655, d145878, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d11669 q = 1) (hb : d142666 q = 1) : d145892 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d11669, d145892, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d11669, d145892, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro26553 (p : Pattern) (ha : d11670 p = 1) (hb : d142666 p = 1) : d145893 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d142666 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d11651 q = 1) (hb : d142666 q = 1) : d145874 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d11651, d145874, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26548 q ha hb
    | true =>
      simp only [d11651, d145874, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d11652 q = 1) (hb : d142666 q = 1) : d145875 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d11652, d145875, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11652, d145875, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d11657 q = 1) (hb : d142666 q = 1) : d145880 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d11657, d145880, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d11657, d145880, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d11658 q = 1) (hb : d142666 q = 1) : d145881 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d11658, d145881, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d11658, d145881, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d11659 q = 1) (hb : d142666 q = 1) : d145882 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d11659, d145882, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d11659, d145882, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d11670 q = 1) (hb : d142666 q = 1) : d145893 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d11670, d145893, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d11670, d145893, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro26554 (p : Pattern) (ha : d11676 p = 1) (hb : d142666 p = 1) : d145899 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d142666 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d11661 q = 1) (hb : d142666 q = 1) : d145884 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d11661, d145884, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26549 q ha hb
    | true =>
      simp only [d11661, d145884, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26550 q ha hb
  have h2 (q : Pattern) (ha : d11662 q = 1) (hb : d142666 q = 1) : d145885 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d11662, d145885, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11662, d145885, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d11663 q = 1) (hb : d142666 q = 1) : d145886 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d11663, d145886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d11663, d145886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d11664 q = 1) (hb : d142666 q = 1) : d145887 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d11664, d145887, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11664, d145887, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d11665 q = 1) (hb : d142666 q = 1) : d145888 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d11665, d145888, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11665, d145888, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d11671 q = 1) (hb : d142666 q = 1) : d145894 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d11671, d145894, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26552 q ha hb
    | true =>
      simp only [d11671, d145894, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26553 q ha hb
  have h7 (q : Pattern) (ha : d11672 q = 1) (hb : d142666 q = 1) : d145895 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d11672, d145895, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11672, d145895, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d11673 q = 1) (hb : d142666 q = 1) : d145896 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d11673, d145896, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d11673, d145896, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d11674 q = 1) (hb : d142666 q = 1) : d145897 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d11674, d145897, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11674, d145897, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d11675 q = 1) (hb : d142666 q = 1) : d145898 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d11675, d145898, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11675, d145898, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d11676 q = 1) (hb : d142666 q = 1) : d145899 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d11676, d145899, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d11676, d145899, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro26555 (p : Pattern) (ha : d11784 p = 1) (hb : d142666 p = 1) : d145981 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d142666 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d11661 q = 1) (hb : d142666 q = 1) : d145884 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d11661, d145884, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26549 q ha hb
    | true =>
      simp only [d11661, d145884, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26550 q ha hb
  have h2 (q : Pattern) (ha : d11662 q = 1) (hb : d142666 q = 1) : d145885 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d11662, d145885, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11662, d145885, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d11663 q = 1) (hb : d142666 q = 1) : d145886 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d11663, d145886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d11663, d145886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d11664 q = 1) (hb : d142666 q = 1) : d145887 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d11664, d145887, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11664, d145887, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d11665 q = 1) (hb : d142666 q = 1) : d145888 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d11665, d145888, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11665, d145888, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d11779 q = 1) (hb : d142666 q = 1) : d145976 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d11779, d145976, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26550 q ha hb
    | true =>
      simp only [d11779, d145976, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d11780 q = 1) (hb : d142666 q = 1) : d145977 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d11780, d145977, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11780, d145977, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d11781 q = 1) (hb : d142666 q = 1) : d145978 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d11781, d145978, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d11781, d145978, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d11782 q = 1) (hb : d142666 q = 1) : d145979 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d11782, d145979, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11782, d145979, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d11783 q = 1) (hb : d142666 q = 1) : d145980 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d11783, d145980, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11783, d145980, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d11784 q = 1) (hb : d142666 q = 1) : d145981 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d11784, d145981, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d11784, d145981, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro26556 (p : Pattern) (ha : d11790 p = 1) (hb : d142666 p = 1) : d145987 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d142666 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d11779 q = 1) (hb : d142666 q = 1) : d145976 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d11779, d145976, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26550 q ha hb
    | true =>
      simp only [d11779, d145976, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d11780 q = 1) (hb : d142666 q = 1) : d145977 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d11780, d145977, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11780, d145977, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d11781 q = 1) (hb : d142666 q = 1) : d145978 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d11781, d145978, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d11781, d145978, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d11782 q = 1) (hb : d142666 q = 1) : d145979 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d11782, d145979, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11782, d145979, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d11783 q = 1) (hb : d142666 q = 1) : d145980 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d11783, d145980, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11783, d145980, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d11785 q = 1) (hb : d142666 q = 1) : d145982 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d11785, d145982, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26553 q ha hb
    | true =>
      simp only [d11785, d145982, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d11786 q = 1) (hb : d142666 q = 1) : d145983 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d11786, d145983, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11786, d145983, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d11787 q = 1) (hb : d142666 q = 1) : d145984 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d11787, d145984, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d11787, d145984, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d11788 q = 1) (hb : d142666 q = 1) : d145985 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d11788, d145985, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11788, d145985, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d11789 q = 1) (hb : d142666 q = 1) : d145986 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d11789, d145986, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11789, d145986, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d11790 q = 1) (hb : d142666 q = 1) : d145987 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d11790, d145987, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d11790, d145987, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro26557 (p : Pattern) (ha : d11799 p = 1) (hb : d142666 p = 1) : d145996 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d142666 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d11785 q = 1) (hb : d142666 q = 1) : d145982 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d11785, d145982, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26553 q ha hb
    | true =>
      simp only [d11785, d145982, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d11786 q = 1) (hb : d142666 q = 1) : d145983 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d11786, d145983, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11786, d145983, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d11787 q = 1) (hb : d142666 q = 1) : d145984 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d11787, d145984, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d11787, d145984, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d11788 q = 1) (hb : d142666 q = 1) : d145985 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d11788, d145985, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11788, d145985, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d11789 q = 1) (hb : d142666 q = 1) : d145986 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d11789, d145986, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11789, d145986, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d11799 q = 1) (hb : d142666 q = 1) : d145996 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d11799, d145996, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11799, d145996, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro26558 (p : Pattern) (ha : d1878 p = 1) (hb : d142665 p = 1) : d146011 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1872 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1877 q = 1) (hb : d122304 q = 1) : d1877 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d1878 q = 1) (hb : d142665 q = 1) : d146011 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d1878, d142665, d146011, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d1878, d142665, d146011, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  exact h2 p ha hb
theorem andIntro26559 (p : Pattern) (ha : d11830 p = 1) (hb : d142666 p = 1) : d146030 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d142666 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d11812 q = 1) (hb : d142666 q = 1) : d146012 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d11812, d142666, d146012, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26558 q ha hb
    | true =>
      simp only [d11812, d142666, d146012, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d11813 q = 1) (hb : d142666 q = 1) : d146013 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d11813, d146013, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11813, d146013, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d11814 q = 1) (hb : d142666 q = 1) : d146014 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d11814, d146014, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11814, d146014, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d11820 q = 1) (hb : d142666 q = 1) : d146020 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d11820, d146020, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d11820, d146020, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d11829 q = 1) (hb : d142666 q = 1) : d146029 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d11829, d146029, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d11829, d146029, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d11830 q = 1) (hb : d142666 q = 1) : d146030 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d11830, d146030, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d11830, d146030, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h7 p ha hb
theorem andIntro26560 (p : Pattern) (ha : d11886 p = 1) (hb : d142666 p = 1) : d146062 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d142666 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d11831 q = 1) (hb : d142666 q = 1) : d146031 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d11831, d146031, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26559 q ha hb
    | true =>
      simp only [d11831, d146031, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d11832 q = 1) (hb : d142666 q = 1) : d146032 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d11832, d146032, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11832, d146032, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d11883 q = 1) (hb : d142666 q = 1) : d146059 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d11883, d146059, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d11883, d146059, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d11884 q = 1) (hb : d142666 q = 1) : d146060 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d11884, d146060, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d11884, d146060, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d11885 q = 1) (hb : d142666 q = 1) : d146061 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d11885, d146061, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d11885, d146061, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d11886 q = 1) (hb : d142666 q = 1) : d146062 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d11886, d146062, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d11886, d146062, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro26561 (p : Pattern) (ha : d11892 p = 1) (hb : d142666 p = 1) : d146068 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d142666 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d11887 q = 1) (hb : d142666 q = 1) : d146063 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d11887, d146063, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26560 q ha hb
    | true =>
      simp only [d11887, d146063, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d11888 q = 1) (hb : d142666 q = 1) : d146064 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d11888, d146064, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11888, d146064, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d11889 q = 1) (hb : d142666 q = 1) : d146065 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d11889, d146065, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d11889, d146065, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d11890 q = 1) (hb : d142666 q = 1) : d146066 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d11890, d146066, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11890, d146066, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d11891 q = 1) (hb : d142666 q = 1) : d146067 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d11891, d146067, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11891, d146067, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d11892 q = 1) (hb : d142666 q = 1) : d146068 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d11892, d146068, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11892, d146068, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro26562 (p : Pattern) (ha : d11681 p = 1) (hb : d142666 p = 1) : d145904 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d142666 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d11647 q = 1) (hb : d142666 q = 1) : d145870 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d11647, d145870, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26547 q ha hb
    | true =>
      simp only [d11647, d145870, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d11648 q = 1) (hb : d142666 q = 1) : d145871 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d11648, d145871, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11648, d145871, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d11651 q = 1) (hb : d142666 q = 1) : d145874 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d11651, d145874, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26548 q ha hb
    | true =>
      simp only [d11651, d145874, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d11652 q = 1) (hb : d142666 q = 1) : d145875 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d11652, d145875, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11652, d145875, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d11653 q = 1) (hb : d142666 q = 1) : d145876 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d11653, d145876, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d11653, d145876, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d11654 q = 1) (hb : d142666 q = 1) : d145877 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d11654, d145877, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d11654, d145877, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d11680 q = 1) (hb : d142666 q = 1) : d145903 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d11680, d145903, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11680, d145903, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d11681 q = 1) (hb : d142666 q = 1) : d145904 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d11681, d145904, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11681, d145904, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro26563 (p : Pattern) (ha : d11683 p = 1) (hb : d142666 p = 1) : d145906 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d142666 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d11651 q = 1) (hb : d142666 q = 1) : d145874 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d11651, d145874, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26548 q ha hb
    | true =>
      simp only [d11651, d145874, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d11652 q = 1) (hb : d142666 q = 1) : d145875 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d11652, d145875, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11652, d145875, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d11657 q = 1) (hb : d142666 q = 1) : d145880 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d11657, d145880, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d11657, d145880, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d11658 q = 1) (hb : d142666 q = 1) : d145881 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d11658, d145881, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d11658, d145881, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d11682 q = 1) (hb : d142666 q = 1) : d145905 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d11682, d145905, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11682, d145905, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d11683 q = 1) (hb : d142666 q = 1) : d145906 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d11683, d145906, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11683, d145906, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro26564 (p : Pattern) (ha : d11690 p = 1) (hb : d142666 p = 1) : d145913 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d142666 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d11647 q = 1) (hb : d142666 q = 1) : d145870 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d11647, d145870, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26547 q ha hb
    | true =>
      simp only [d11647, d145870, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d11648 q = 1) (hb : d142666 q = 1) : d145871 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d11648, d145871, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11648, d145871, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d11651 q = 1) (hb : d142666 q = 1) : d145874 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d11651, d145874, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26548 q ha hb
    | true =>
      simp only [d11651, d145874, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d11652 q = 1) (hb : d142666 q = 1) : d145875 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d11652, d145875, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11652, d145875, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d11653 q = 1) (hb : d142666 q = 1) : d145876 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d11653, d145876, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d11653, d145876, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d11688 q = 1) (hb : d142666 q = 1) : d145911 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d11688, d145911, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11688, d145911, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d11689 q = 1) (hb : d142666 q = 1) : d145912 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d11689, d145912, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d11689, d145912, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d11690 q = 1) (hb : d142666 q = 1) : d145913 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d11690, d145913, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11690, d145913, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro26565 (p : Pattern) (ha : d11693 p = 1) (hb : d142666 p = 1) : d145916 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d142666 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d11651 q = 1) (hb : d142666 q = 1) : d145874 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d11651, d145874, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26548 q ha hb
    | true =>
      simp only [d11651, d145874, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d11652 q = 1) (hb : d142666 q = 1) : d145875 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d11652, d145875, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11652, d145875, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d11657 q = 1) (hb : d142666 q = 1) : d145880 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d11657, d145880, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d11657, d145880, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d11691 q = 1) (hb : d142666 q = 1) : d145914 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d11691, d145914, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11691, d145914, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d11692 q = 1) (hb : d142666 q = 1) : d145915 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d11692, d145915, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d11692, d145915, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d11693 q = 1) (hb : d142666 q = 1) : d145916 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d11693, d145916, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11693, d145916, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro26566 (p : Pattern) (ha : d1670 p = 1) (hb : d142665 p = 1) : d145920 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1669 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1 q = 1) (hb : d1558 q = 1) : d1558 q = 1 := by
    exact hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d1573 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d1574 q = 1) (hb : d122304 q = 1) : d15150 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d1574, d122304, d15150, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d1574, d122304, d15150, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d1670 q = 1) (hb : d142665 q = 1) : d145920 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d1670, d142665, d145920, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d1670, d142665, d145920, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  exact h4 p ha hb
theorem andIntro26567 (p : Pattern) (ha : d11702 p = 1) (hb : d142666 p = 1) : d145926 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d142666 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d11697 q = 1) (hb : d142666 q = 1) : d145921 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d11697, d142666, d145921, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26566 q ha hb
    | true =>
      simp only [d11697, d142666, d145921, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d11698 q = 1) (hb : d142666 q = 1) : d145922 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d11698, d145922, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11698, d145922, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d11699 q = 1) (hb : d142666 q = 1) : d145923 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d11699, d145923, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11699, d145923, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d11637 q = 1) (hb : d142666 q = 1) : d145859 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d11637, d142666, d145859, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26545 q ha hb
    | true =>
      simp only [d11637, d142666, d145859, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h6 (q : Pattern) (ha : d11638 q = 1) (hb : d142666 q = 1) : d145860 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d11638, d145860, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11638, d145860, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d11639 q = 1) (hb : d142666 q = 1) : d145861 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d11639, d145861, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11639, d145861, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d11700 q = 1) (hb : d142666 q = 1) : d145924 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d11700, d145924, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d11700, d145924, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d11640 q = 1) (hb : d142666 q = 1) : d145863 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d11640, d142666, d145863, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26546 q ha hb
    | true =>
      simp only [d11640, d142666, d145863, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h10 (q : Pattern) (ha : d11641 q = 1) (hb : d142666 q = 1) : d145864 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d11641, d145864, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11641, d145864, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d11642 q = 1) (hb : d142666 q = 1) : d145865 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d11642, d145865, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11642, d145865, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d11643 q = 1) (hb : d142666 q = 1) : d145866 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d11643, d145866, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d11643, d145866, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d11701 q = 1) (hb : d142666 q = 1) : d145925 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d11701, d145925, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d11701, d145925, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d11702 q = 1) (hb : d142666 q = 1) : d145926 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d11702, d145926, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d11702, d145926, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h14 p ha hb
theorem andIntro26568 (p : Pattern) (ha : d11708 p = 1) (hb : d142666 p = 1) : d145932 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d142666 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d11703 q = 1) (hb : d142666 q = 1) : d145927 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d11703, d145927, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26567 q ha hb
    | true =>
      simp only [d11703, d145927, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d11704 q = 1) (hb : d142666 q = 1) : d145928 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d11704, d145928, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11704, d145928, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d11647 q = 1) (hb : d142666 q = 1) : d145870 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d11647, d145870, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26547 q ha hb
    | true =>
      simp only [d11647, d145870, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d11648 q = 1) (hb : d142666 q = 1) : d145871 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d11648, d145871, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11648, d145871, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d11705 q = 1) (hb : d142666 q = 1) : d145929 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d11705, d145929, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d11705, d145929, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d11706 q = 1) (hb : d142666 q = 1) : d145930 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d11706, d145930, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d11706, d145930, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d11707 q = 1) (hb : d142666 q = 1) : d145931 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d11707, d145931, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d11707, d145931, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d11708 q = 1) (hb : d142666 q = 1) : d145932 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d11708, d145932, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11708, d145932, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro26569 (p : Pattern) (ha : d5635 p = 1) (hb : d142665 p = 1) : d145935 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1586 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d5634 q = 1) (hb : d122304 q = 1) : d5634 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d5635 q = 1) (hb : d142665 q = 1) : d145935 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d5635, d142665, d145935, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d5635, d142665, d145935, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  exact h2 p ha hb
theorem andIntro26570 (p : Pattern) (ha : d11741 p = 1) (hb : d142666 p = 1) : d145941 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d142666 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d11637 q = 1) (hb : d142666 q = 1) : d145859 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d11637, d142666, d145859, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26545 q ha hb
    | true =>
      simp only [d11637, d142666, d145859, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d11638 q = 1) (hb : d142666 q = 1) : d145860 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d11638, d145860, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11638, d145860, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d11639 q = 1) (hb : d142666 q = 1) : d145861 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d11639, d145861, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11639, d145861, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d11640 q = 1) (hb : d142666 q = 1) : d145863 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d11640, d142666, d145863, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26546 q ha hb
    | true =>
      simp only [d11640, d142666, d145863, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h6 (q : Pattern) (ha : d11641 q = 1) (hb : d142666 q = 1) : d145864 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d11641, d145864, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11641, d145864, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d11642 q = 1) (hb : d142666 q = 1) : d145865 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d11642, d145865, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11642, d145865, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d11643 q = 1) (hb : d142666 q = 1) : d145866 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d11643, d145866, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d11643, d145866, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d11736 q = 1) (hb : d142666 q = 1) : d145936 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d11736, d142666, d145936, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26569 q ha hb
    | true =>
      simp only [d11736, d142666, d145936, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h10 (q : Pattern) (ha : d11737 q = 1) (hb : d142666 q = 1) : d145937 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d11737, d145937, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11737, d145937, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d11738 q = 1) (hb : d142666 q = 1) : d145938 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d11738, d145938, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11738, d145938, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d11739 q = 1) (hb : d142666 q = 1) : d145939 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d11739, d145939, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d11739, d145939, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d11740 q = 1) (hb : d142666 q = 1) : d145940 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d11740, d145940, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d11740, d145940, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d11741 q = 1) (hb : d142666 q = 1) : d145941 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d11741, d145941, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d11741, d145941, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h14 p ha hb
theorem andIntro26571 (p : Pattern) (ha : d11747 p = 1) (hb : d142666 p = 1) : d145947 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d142666 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d11742 q = 1) (hb : d142666 q = 1) : d145942 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d11742, d145942, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26570 q ha hb
    | true =>
      simp only [d11742, d145942, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d11743 q = 1) (hb : d142666 q = 1) : d145943 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d11743, d145943, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11743, d145943, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d11744 q = 1) (hb : d142666 q = 1) : d145944 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d11744, d145944, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d11744, d145944, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d11745 q = 1) (hb : d142666 q = 1) : d145945 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d11745, d145945, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d11745, d145945, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d11746 q = 1) (hb : d142666 q = 1) : d145946 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d11746, d145946, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d11746, d145946, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d11747 q = 1) (hb : d142666 q = 1) : d145947 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d11747, d145947, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11747, d145947, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro26572 (p : Pattern) (ha : d108984 p = 1) (hb : d142666 p = 1) : d145953 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d142666 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d11684 q = 1) (hb : d142666 q = 1) : d145907 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d11684, d145907, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26562 q ha hb
    | true =>
      simp only [d11684, d145907, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26563 q ha hb
  have h2 (q : Pattern) (ha : d11685 q = 1) (hb : d142666 q = 1) : d145908 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d11685, d145908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11685, d145908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d11686 q = 1) (hb : d142666 q = 1) : d145909 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d11686, d145909, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d11686, d145909, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d11687 q = 1) (hb : d142666 q = 1) : d145910 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d11687, d145910, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11687, d145910, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d11694 q = 1) (hb : d142666 q = 1) : d145917 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d11694, d145917, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26564 q ha hb
    | true =>
      simp only [d11694, d145917, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26565 q ha hb
  have h6 (q : Pattern) (ha : d11695 q = 1) (hb : d142666 q = 1) : d145918 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d11695, d145918, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11695, d145918, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d11696 q = 1) (hb : d142666 q = 1) : d145919 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d11696, d145919, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d11696, d145919, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d11709 q = 1) (hb : d142666 q = 1) : d145933 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d11709, d145933, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26568 q ha hb
    | true =>
      simp only [d11709, d145933, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26549 q ha hb
  have h9 (q : Pattern) (ha : d108980 q = 1) (hb : d142666 q = 1) : d145934 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d108980, d145934, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d108980, d145934, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d11748 q = 1) (hb : d142666 q = 1) : d145948 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d11748, d145948, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26571 q ha hb
    | true =>
      simp only [d11748, d145948, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d11749 q = 1) (hb : d142666 q = 1) : d145949 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d11749, d145949, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d11749, d145949, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d108981 q = 1) (hb : d142666 q = 1) : d145950 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d108981, d145950, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d108981, d145950, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d108982 q = 1) (hb : d142666 q = 1) : d145951 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d108982, d145951, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d108982, d145951, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d108983 q = 1) (hb : d142666 q = 1) : d145952 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d108983, d145952, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d108983, d145952, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d108984 q = 1) (hb : d142666 q = 1) : d145953 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d108984, d145953, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d108984, d145953, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro26573 (p : Pattern) (ha : d11754 p = 1) (hb : d142666 p = 1) : d145954 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d142666 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d11647 q = 1) (hb : d142666 q = 1) : d145870 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d11647, d145870, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26547 q ha hb
    | true =>
      simp only [d11647, d145870, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d11648 q = 1) (hb : d142666 q = 1) : d145871 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d11648, d145871, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11648, d145871, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d11651 q = 1) (hb : d142666 q = 1) : d145874 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d11651, d145874, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26548 q ha hb
    | true =>
      simp only [d11651, d145874, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d11652 q = 1) (hb : d142666 q = 1) : d145875 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d11652, d145875, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11652, d145875, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d11653 q = 1) (hb : d142666 q = 1) : d145876 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d11653, d145876, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d11653, d145876, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d11654 q = 1) (hb : d142666 q = 1) : d145877 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d11654, d145877, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d11654, d145877, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d11680 q = 1) (hb : d142666 q = 1) : d145903 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d11680, d145903, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11680, d145903, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d11754 q = 1) (hb : d142666 q = 1) : d145954 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d11754, d145954, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d11754, d145954, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro26574 (p : Pattern) (ha : d11755 p = 1) (hb : d142666 p = 1) : d145955 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d142666 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d11651 q = 1) (hb : d142666 q = 1) : d145874 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d11651, d145874, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26548 q ha hb
    | true =>
      simp only [d11651, d145874, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d11652 q = 1) (hb : d142666 q = 1) : d145875 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d11652, d145875, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11652, d145875, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d11657 q = 1) (hb : d142666 q = 1) : d145880 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d11657, d145880, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d11657, d145880, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d11658 q = 1) (hb : d142666 q = 1) : d145881 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d11658, d145881, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d11658, d145881, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d11682 q = 1) (hb : d142666 q = 1) : d145905 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d11682, d145905, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11682, d145905, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d11755 q = 1) (hb : d142666 q = 1) : d145955 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d11755, d145955, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d11755, d145955, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro26575 (p : Pattern) (ha : d11760 p = 1) (hb : d142666 p = 1) : d145960 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d142666 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d11647 q = 1) (hb : d142666 q = 1) : d145870 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d11647, d145870, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26547 q ha hb
    | true =>
      simp only [d11647, d145870, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d11648 q = 1) (hb : d142666 q = 1) : d145871 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d11648, d145871, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11648, d145871, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d11651 q = 1) (hb : d142666 q = 1) : d145874 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d11651, d145874, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26548 q ha hb
    | true =>
      simp only [d11651, d145874, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d11652 q = 1) (hb : d142666 q = 1) : d145875 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d11652, d145875, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11652, d145875, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d11653 q = 1) (hb : d142666 q = 1) : d145876 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d11653, d145876, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d11653, d145876, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d11688 q = 1) (hb : d142666 q = 1) : d145911 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d11688, d145911, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11688, d145911, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d11689 q = 1) (hb : d142666 q = 1) : d145912 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d11689, d145912, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d11689, d145912, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d11760 q = 1) (hb : d142666 q = 1) : d145960 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d11760, d145960, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d11760, d145960, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro26576 (p : Pattern) (ha : d11761 p = 1) (hb : d142666 p = 1) : d145961 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d142666 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d11651 q = 1) (hb : d142666 q = 1) : d145874 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d11651, d145874, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26548 q ha hb
    | true =>
      simp only [d11651, d145874, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d11652 q = 1) (hb : d142666 q = 1) : d145875 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d11652, d145875, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11652, d145875, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d11657 q = 1) (hb : d142666 q = 1) : d145880 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d11657, d145880, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d11657, d145880, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d11691 q = 1) (hb : d142666 q = 1) : d145914 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d11691, d145914, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11691, d145914, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d11692 q = 1) (hb : d142666 q = 1) : d145915 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d11692, d145915, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d11692, d145915, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d11761 q = 1) (hb : d142666 q = 1) : d145961 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d11761, d145961, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d11761, d145961, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro26577 (p : Pattern) (ha : d11765 p = 1) (hb : d142666 p = 1) : d145965 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d142666 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d11703 q = 1) (hb : d142666 q = 1) : d145927 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d11703, d145927, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26567 q ha hb
    | true =>
      simp only [d11703, d145927, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d11704 q = 1) (hb : d142666 q = 1) : d145928 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d11704, d145928, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11704, d145928, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d11647 q = 1) (hb : d142666 q = 1) : d145870 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d11647, d145870, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26547 q ha hb
    | true =>
      simp only [d11647, d145870, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d11648 q = 1) (hb : d142666 q = 1) : d145871 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d11648, d145871, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11648, d145871, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d11705 q = 1) (hb : d142666 q = 1) : d145929 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d11705, d145929, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d11705, d145929, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d11706 q = 1) (hb : d142666 q = 1) : d145930 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d11706, d145930, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d11706, d145930, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d11707 q = 1) (hb : d142666 q = 1) : d145931 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d11707, d145931, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d11707, d145931, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d11765 q = 1) (hb : d142666 q = 1) : d145965 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d11765, d145965, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d11765, d145965, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro26578 (p : Pattern) (ha : d11771 p = 1) (hb : d142666 p = 1) : d145968 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d142666 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d11742 q = 1) (hb : d142666 q = 1) : d145942 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d11742, d145942, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26570 q ha hb
    | true =>
      simp only [d11742, d145942, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d11743 q = 1) (hb : d142666 q = 1) : d145943 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d11743, d145943, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11743, d145943, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d11744 q = 1) (hb : d142666 q = 1) : d145944 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d11744, d145944, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d11744, d145944, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d11745 q = 1) (hb : d142666 q = 1) : d145945 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d11745, d145945, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d11745, d145945, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d11746 q = 1) (hb : d142666 q = 1) : d145946 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d11746, d145946, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d11746, d145946, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d11771 q = 1) (hb : d142666 q = 1) : d145968 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d11771, d145968, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d11771, d145968, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro26579 (p : Pattern) (ha : d108989 p = 1) (hb : d142666 p = 1) : d145974 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d142666 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d11684 q = 1) (hb : d142666 q = 1) : d145907 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d11684, d145907, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26562 q ha hb
    | true =>
      simp only [d11684, d145907, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26563 q ha hb
  have h2 (q : Pattern) (ha : d11685 q = 1) (hb : d142666 q = 1) : d145908 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d11685, d145908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11685, d145908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d11686 q = 1) (hb : d142666 q = 1) : d145909 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d11686, d145909, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d11686, d145909, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d11687 q = 1) (hb : d142666 q = 1) : d145910 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d11687, d145910, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11687, d145910, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d11694 q = 1) (hb : d142666 q = 1) : d145917 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d11694, d145917, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26564 q ha hb
    | true =>
      simp only [d11694, d145917, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26565 q ha hb
  have h6 (q : Pattern) (ha : d11695 q = 1) (hb : d142666 q = 1) : d145918 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d11695, d145918, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11695, d145918, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d11696 q = 1) (hb : d142666 q = 1) : d145919 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d11696, d145919, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d11696, d145919, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d11709 q = 1) (hb : d142666 q = 1) : d145933 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d11709, d145933, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26568 q ha hb
    | true =>
      simp only [d11709, d145933, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26549 q ha hb
  have h9 (q : Pattern) (ha : d108980 q = 1) (hb : d142666 q = 1) : d145934 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d108980, d145934, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d108980, d145934, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d11748 q = 1) (hb : d142666 q = 1) : d145948 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d11748, d145948, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26571 q ha hb
    | true =>
      simp only [d11748, d145948, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d11749 q = 1) (hb : d142666 q = 1) : d145949 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d11749, d145949, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d11749, d145949, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d108981 q = 1) (hb : d142666 q = 1) : d145950 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d108981, d145950, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d108981, d145950, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d108982 q = 1) (hb : d142666 q = 1) : d145951 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d108982, d145951, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d108982, d145951, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d108983 q = 1) (hb : d142666 q = 1) : d145952 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d108983, d145952, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d108983, d145952, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d11756 q = 1) (hb : d142666 q = 1) : d145956 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d11756, d145956, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26573 q ha hb
    | true =>
      simp only [d11756, d145956, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26574 q ha hb
  have h16 (q : Pattern) (ha : d11757 q = 1) (hb : d142666 q = 1) : d145957 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d11757, d145957, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11757, d145957, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d11758 q = 1) (hb : d142666 q = 1) : d145958 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d11758, d145958, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d11758, d145958, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h18 (q : Pattern) (ha : d11759 q = 1) (hb : d142666 q = 1) : d145959 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d11759, d145959, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11759, d145959, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d11762 q = 1) (hb : d142666 q = 1) : d145962 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d11762, d145962, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26575 q ha hb
    | true =>
      simp only [d11762, d145962, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26576 q ha hb
  have h20 (q : Pattern) (ha : d11763 q = 1) (hb : d142666 q = 1) : d145963 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d11763, d145963, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11763, d145963, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
  have h21 (q : Pattern) (ha : d11764 q = 1) (hb : d142666 q = 1) : d145964 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d11764, d145964, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d11764, d145964, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h22 (q : Pattern) (ha : d11766 q = 1) (hb : d142666 q = 1) : d145966 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d11766, d145966, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26577 q ha hb
    | true =>
      simp only [d11766, d145966, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26552 q ha hb
  have h23 (q : Pattern) (ha : d108985 q = 1) (hb : d142666 q = 1) : d145967 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d108985, d145967, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
    | true =>
      simp only [d108985, d145967, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h24 (q : Pattern) (ha : d11772 q = 1) (hb : d142666 q = 1) : d145969 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d11772, d145969, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26578 q ha hb
    | true =>
      simp only [d11772, d145969, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h25 (q : Pattern) (ha : d11773 q = 1) (hb : d142666 q = 1) : d145970 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d11773, d145970, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q ha hb
    | true =>
      simp only [d11773, d145970, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h26 (q : Pattern) (ha : d108986 q = 1) (hb : d142666 q = 1) : d145971 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d108986, d145971, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
    | true =>
      simp only [d108986, d145971, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q ha hb
  have h27 (q : Pattern) (ha : d108987 q = 1) (hb : d142666 q = 1) : d145972 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d108987, d145972, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d108987, d145972, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h26 q ha hb
  have h28 (q : Pattern) (ha : d108988 q = 1) (hb : d142666 q = 1) : d145973 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d108988, d145973, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d108988, d145973, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h27 q ha hb
  have h29 (q : Pattern) (ha : d108989 q = 1) (hb : d142666 q = 1) : d145974 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d108989, d145974, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d108989, d145974, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h28 q ha hb
  exact h29 p ha hb
theorem andIntro26580 (p : Pattern) (ha : d108996 p = 1) (hb : d142666 p = 1) : d145994 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d142666 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d11766 q = 1) (hb : d142666 q = 1) : d145966 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d11766, d145966, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26577 q ha hb
    | true =>
      simp only [d11766, d145966, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26552 q ha hb
  have h2 (q : Pattern) (ha : d108985 q = 1) (hb : d142666 q = 1) : d145967 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d108985, d145967, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d108985, d145967, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d11772 q = 1) (hb : d142666 q = 1) : d145969 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d11772, d145969, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26578 q ha hb
    | true =>
      simp only [d11772, d145969, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d11773 q = 1) (hb : d142666 q = 1) : d145970 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d11773, d145970, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d11773, d145970, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d108986 q = 1) (hb : d142666 q = 1) : d145971 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d108986, d145971, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d108986, d145971, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d108994 q = 1) (hb : d142666 q = 1) : d145992 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d108994, d145992, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d108994, d145992, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d108995 q = 1) (hb : d142666 q = 1) : d145993 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d108995, d145993, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d108995, d145993, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d108996 q = 1) (hb : d142666 q = 1) : d145994 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d108996, d145994, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d108996, d145994, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro26581 (p : Pattern) (ha : d1867 p = 1) (hb : d142665 p = 1) : d146002 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1861 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1 q = 1) (hb : d1860 q = 1) : d1860 q = 1 := by
    exact hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d1865 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d1866 q = 1) (hb : d122304 q = 1) : d15386 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d1866, d122304, d15386, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d1866, d122304, d15386, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d1867 q = 1) (hb : d142665 q = 1) : d146002 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d1867, d142665, d146002, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d1867, d142665, d146002, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  exact h4 p ha hb
theorem andIntro26582 (p : Pattern) (ha : d1873 p = 1) (hb : d142665 p = 1) : d146006 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1866 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1 q = 1) (hb : d1865 q = 1) : d1865 q = 1 := by
    exact hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d1871 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d1872 q = 1) (hb : d122304 q = 1) : d15407 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d1872, d122304, d15407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d1872, d122304, d15407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d1873 q = 1) (hb : d142665 q = 1) : d146006 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d1873, d142665, d146006, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d1873, d142665, d146006, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  exact h4 p ha hb
theorem andIntro26583 (p : Pattern) (ha : d11817 p = 1) (hb : d142666 p = 1) : d146017 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d142666 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d11805 q = 1) (hb : d142666 q = 1) : d146003 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d11805, d142666, d146003, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26581 q ha hb
    | true =>
      simp only [d11805, d142666, d146003, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d11806 q = 1) (hb : d142666 q = 1) : d146004 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d11806, d146004, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11806, d146004, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d11807 q = 1) (hb : d142666 q = 1) : d146005 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d11807, d146005, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11807, d146005, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d11808 q = 1) (hb : d142666 q = 1) : d146007 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d11808, d142666, d146007, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26582 q ha hb
    | true =>
      simp only [d11808, d142666, d146007, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h6 (q : Pattern) (ha : d11809 q = 1) (hb : d142666 q = 1) : d146008 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d11809, d146008, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11809, d146008, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d11810 q = 1) (hb : d142666 q = 1) : d146009 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d11810, d146009, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11810, d146009, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d11811 q = 1) (hb : d142666 q = 1) : d146010 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d11811, d146010, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d11811, d146010, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d11812 q = 1) (hb : d142666 q = 1) : d146012 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d11812, d142666, d146012, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26558 q ha hb
    | true =>
      simp only [d11812, d142666, d146012, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h10 (q : Pattern) (ha : d11813 q = 1) (hb : d142666 q = 1) : d146013 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d11813, d146013, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11813, d146013, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d11814 q = 1) (hb : d142666 q = 1) : d146014 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d11814, d146014, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11814, d146014, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d11815 q = 1) (hb : d142666 q = 1) : d146015 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d11815, d146015, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d11815, d146015, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d11816 q = 1) (hb : d142666 q = 1) : d146016 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d11816, d146016, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d11816, d146016, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d11817 q = 1) (hb : d142666 q = 1) : d146017 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d11817, d146017, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d11817, d146017, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h14 p ha hb
theorem andIntro26584 (p : Pattern) (ha : d11822 p = 1) (hb : d142666 p = 1) : d146022 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d142666 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d11808 q = 1) (hb : d142666 q = 1) : d146007 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d11808, d142666, d146007, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26582 q ha hb
    | true =>
      simp only [d11808, d142666, d146007, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d11809 q = 1) (hb : d142666 q = 1) : d146008 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d11809, d146008, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11809, d146008, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d11810 q = 1) (hb : d142666 q = 1) : d146009 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d11810, d146009, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11810, d146009, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d11812 q = 1) (hb : d142666 q = 1) : d146012 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d11812, d142666, d146012, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26558 q ha hb
    | true =>
      simp only [d11812, d142666, d146012, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h6 (q : Pattern) (ha : d11813 q = 1) (hb : d142666 q = 1) : d146013 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d11813, d146013, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11813, d146013, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d11814 q = 1) (hb : d142666 q = 1) : d146014 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d11814, d146014, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11814, d146014, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d11815 q = 1) (hb : d142666 q = 1) : d146015 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d11815, d146015, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d11815, d146015, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d11820 q = 1) (hb : d142666 q = 1) : d146020 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d11820, d146020, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d11820, d146020, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d11821 q = 1) (hb : d142666 q = 1) : d146021 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d11821, d146021, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d11821, d146021, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d11822 q = 1) (hb : d142666 q = 1) : d146022 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d11822, d146022, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d11822, d146022, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h11 p ha hb
theorem andIntro26585 (p : Pattern) (ha : d11828 p = 1) (hb : d142666 p = 1) : d146028 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d142666 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d11818 q = 1) (hb : d142666 q = 1) : d146018 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d11818, d146018, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26583 q ha hb
    | true =>
      simp only [d11818, d146018, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d11819 q = 1) (hb : d142666 q = 1) : d146019 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d11819, d146019, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11819, d146019, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d11823 q = 1) (hb : d142666 q = 1) : d146023 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d11823, d146023, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26584 q ha hb
    | true =>
      simp only [d11823, d146023, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d11824 q = 1) (hb : d142666 q = 1) : d146024 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d11824, d146024, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11824, d146024, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d11825 q = 1) (hb : d142666 q = 1) : d146025 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d11825, d146025, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d11825, d146025, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d11826 q = 1) (hb : d142666 q = 1) : d146026 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d11826, d146026, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d11826, d146026, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d11827 q = 1) (hb : d142666 q = 1) : d146027 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d11827, d146027, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d11827, d146027, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d11828 q = 1) (hb : d142666 q = 1) : d146028 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d11828, d146028, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d11828, d146028, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro26586 (p : Pattern) (ha : d11836 p = 1) (hb : d142666 p = 1) : d146036 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d142666 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d11823 q = 1) (hb : d142666 q = 1) : d146023 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d11823, d146023, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26584 q ha hb
    | true =>
      simp only [d11823, d146023, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d11824 q = 1) (hb : d142666 q = 1) : d146024 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d11824, d146024, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11824, d146024, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d11831 q = 1) (hb : d142666 q = 1) : d146031 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d11831, d146031, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26559 q ha hb
    | true =>
      simp only [d11831, d146031, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d11832 q = 1) (hb : d142666 q = 1) : d146032 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d11832, d146032, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11832, d146032, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d11833 q = 1) (hb : d142666 q = 1) : d146033 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d11833, d146033, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d11833, d146033, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d11834 q = 1) (hb : d142666 q = 1) : d146034 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d11834, d146034, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d11834, d146034, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d11835 q = 1) (hb : d142666 q = 1) : d146035 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d11835, d146035, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d11835, d146035, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d11836 q = 1) (hb : d142666 q = 1) : d146036 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d11836, d146036, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d11836, d146036, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro26587 (p : Pattern) (ha : d5679 p = 1) (hb : d142665 p = 1) : d146039 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1872 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d5678 q = 1) (hb : d122304 q = 1) : d5678 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d5679 q = 1) (hb : d142665 q = 1) : d146039 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d5679, d142665, d146039, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d5679, d142665, d146039, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  exact h2 p ha hb
theorem andIntro26588 (p : Pattern) (ha : d11869 p = 1) (hb : d142666 p = 1) : d146045 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d142666 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d11808 q = 1) (hb : d142666 q = 1) : d146007 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d11808, d142666, d146007, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26582 q ha hb
    | true =>
      simp only [d11808, d142666, d146007, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d11809 q = 1) (hb : d142666 q = 1) : d146008 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d11809, d146008, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11809, d146008, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d11810 q = 1) (hb : d142666 q = 1) : d146009 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d11810, d146009, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11810, d146009, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d11812 q = 1) (hb : d142666 q = 1) : d146012 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d11812, d142666, d146012, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26558 q ha hb
    | true =>
      simp only [d11812, d142666, d146012, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h6 (q : Pattern) (ha : d11813 q = 1) (hb : d142666 q = 1) : d146013 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d11813, d146013, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11813, d146013, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d11814 q = 1) (hb : d142666 q = 1) : d146014 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d11814, d146014, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11814, d146014, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d11815 q = 1) (hb : d142666 q = 1) : d146015 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d11815, d146015, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d11815, d146015, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d11864 q = 1) (hb : d142666 q = 1) : d146040 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d11864, d142666, d146040, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26587 q ha hb
    | true =>
      simp only [d11864, d142666, d146040, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h10 (q : Pattern) (ha : d11865 q = 1) (hb : d142666 q = 1) : d146041 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d11865, d146041, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11865, d146041, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d11866 q = 1) (hb : d142666 q = 1) : d146042 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d11866, d146042, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11866, d146042, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d11867 q = 1) (hb : d142666 q = 1) : d146043 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d11867, d146043, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d11867, d146043, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d11868 q = 1) (hb : d142666 q = 1) : d146044 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d11868, d146044, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d11868, d146044, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d11869 q = 1) (hb : d142666 q = 1) : d146045 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d11869, d146045, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d11869, d146045, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h14 p ha hb
theorem andIntro26589 (p : Pattern) (ha : d11875 p = 1) (hb : d142666 p = 1) : d146051 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d142666 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d11870 q = 1) (hb : d142666 q = 1) : d146046 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d11870, d146046, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26588 q ha hb
    | true =>
      simp only [d11870, d146046, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d11871 q = 1) (hb : d142666 q = 1) : d146047 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d11871, d146047, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11871, d146047, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d11872 q = 1) (hb : d142666 q = 1) : d146048 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d11872, d146048, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d11872, d146048, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d11873 q = 1) (hb : d142666 q = 1) : d146049 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d11873, d146049, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d11873, d146049, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d11874 q = 1) (hb : d142666 q = 1) : d146050 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d11874, d146050, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d11874, d146050, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d11875 q = 1) (hb : d142666 q = 1) : d146051 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d11875, d146051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d11875, d146051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro26590 (p : Pattern) (ha : d109006 p = 1) (hb : d142666 p = 1) : d146057 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d142666 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d11837 q = 1) (hb : d142666 q = 1) : d146037 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d11837, d146037, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26585 q ha hb
    | true =>
      simp only [d11837, d146037, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26586 q ha hb
  have h2 (q : Pattern) (ha : d109002 q = 1) (hb : d142666 q = 1) : d146038 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d109002, d146038, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d109002, d146038, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d11876 q = 1) (hb : d142666 q = 1) : d146052 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d11876, d146052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26589 q ha hb
    | true =>
      simp only [d11876, d146052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d11877 q = 1) (hb : d142666 q = 1) : d146053 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d11877, d146053, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d11877, d146053, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d109003 q = 1) (hb : d142666 q = 1) : d146054 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d109003, d146054, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d109003, d146054, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d109004 q = 1) (hb : d142666 q = 1) : d146055 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d109004, d146055, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d109004, d146055, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d109005 q = 1) (hb : d142666 q = 1) : d146056 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d109005, d146056, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d109005, d146056, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d109006 q = 1) (hb : d142666 q = 1) : d146057 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d109006, d146057, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d109006, d146057, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro26591 (p : Pattern) (ha : d109012 p = 1) (hb : d142666 p = 1) : d146074 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d142666 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d11667 q = 1) (hb : d142666 q = 1) : d145890 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d11667, d145890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11667, d145890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26551 q ha hb
  have h2 (q : Pattern) (ha : d11668 q = 1) (hb : d142666 q = 1) : d145891 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d11668, d145891, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d11668, d145891, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d11677 q = 1) (hb : d142666 q = 1) : d145900 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d11677, d145900, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26551 q ha hb
    | true =>
      simp only [d11677, d145900, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26554 q ha hb
  have h4 (q : Pattern) (ha : d11678 q = 1) (hb : d142666 q = 1) : d145901 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d11678, d145901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d11678, d145901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d11679 q = 1) (hb : d142666 q = 1) : d145902 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d11679, d145902, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d11679, d145902, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d108990 q = 1) (hb : d142666 q = 1) : d145975 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d108990, d145975, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26572 q ha hb
    | true =>
      simp only [d108990, d145975, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26579 q ha hb
  have h7 (q : Pattern) (ha : d11791 q = 1) (hb : d142666 q = 1) : d145988 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d11791, d145988, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26555 q ha hb
    | true =>
      simp only [d11791, d145988, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26556 q ha hb
  have h8 (q : Pattern) (ha : d108991 q = 1) (hb : d142666 q = 1) : d145989 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d108991, d145989, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d108991, d145989, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d108992 q = 1) (hb : d142666 q = 1) : d145990 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d108992, d145990, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d108992, d145990, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d108993 q = 1) (hb : d142666 q = 1) : d145991 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d108993, d145991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d108993, d145991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d108997 q = 1) (hb : d142666 q = 1) : d145995 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d108997, d145995, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d108997, d145995, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26580 q ha hb
  have h12 (q : Pattern) (ha : d11800 q = 1) (hb : d142666 q = 1) : d145997 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d11800, d145997, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11800, d145997, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26557 q ha hb
  have h13 (q : Pattern) (ha : d108998 q = 1) (hb : d142666 q = 1) : d145998 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d108998, d145998, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d108998, d145998, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d108999 q = 1) (hb : d142666 q = 1) : d145999 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d108999, d145999, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d108999, d145999, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d109000 q = 1) (hb : d142666 q = 1) : d146000 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d109000, d146000, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d109000, d146000, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h16 (q : Pattern) (ha : d109001 q = 1) (hb : d142666 q = 1) : d146001 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d109001, d146001, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d109001, d146001, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d109007 q = 1) (hb : d142666 q = 1) : d146058 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d109007, d146058, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d109007, d146058, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26590 q ha hb
  have h18 (q : Pattern) (ha : d11893 q = 1) (hb : d142666 q = 1) : d146069 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d11893, d146069, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11893, d146069, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26561 q ha hb
  have h19 (q : Pattern) (ha : d109008 q = 1) (hb : d142666 q = 1) : d146070 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d109008, d146070, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d109008, d146070, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d109009 q = 1) (hb : d142666 q = 1) : d146071 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d109009, d146071, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d109009, d146071, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h21 (q : Pattern) (ha : d109010 q = 1) (hb : d142666 q = 1) : d146072 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d109010, d146072, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d109010, d146072, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h22 (q : Pattern) (ha : d109011 q = 1) (hb : d142666 q = 1) : d146073 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d109011, d146073, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d109011, d146073, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h23 (q : Pattern) (ha : d109012 q = 1) (hb : d142666 q = 1) : d146074 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d109012, d146074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d109012, d146074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
  exact h23 p ha hb
theorem andIntro26592 (p : Pattern) (ha : d109018 p = 1) (hb : d142666 p = 1) : d146080 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d142666 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d109013 q = 1) (hb : d142666 q = 1) : d146075 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d109013, d146075, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d109013, d146075, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26591 q ha hb
  have h2 (q : Pattern) (ha : d109014 q = 1) (hb : d142666 q = 1) : d146076 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d109014, d146076, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d109014, d146076, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d109015 q = 1) (hb : d142666 q = 1) : d146077 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d109015, d146077, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d109015, d146077, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d109016 q = 1) (hb : d142666 q = 1) : d146078 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d109016, d146078, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d109016, d146078, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d109017 q = 1) (hb : d142666 q = 1) : d146079 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d109017, d146079, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d109017, d146079, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d109018 q = 1) (hb : d142666 q = 1) : d146080 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d109018, d146080, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d109018, d146080, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro26593 (p : Pattern) (ha : d2070 p = 1) (hb : d142665 p = 1) : d146085 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d2057 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1 q = 1) (hb : d2056 q = 1) : d2056 q = 1 := by
    exact hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d2068 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d2069 q = 1) (hb : d122304 q = 1) : d15547 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d2069, d122304, d15547, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d2069, d122304, d15547, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d2070 q = 1) (hb : d142665 q = 1) : d146085 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d2070, d142665, d146085, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d2070, d142665, d146085, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  exact h4 p ha hb
theorem andIntro26594 (p : Pattern) (ha : d2072 p = 1) (hb : d142665 p = 1) : d146089 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d2069 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d2071 q = 1) (hb : d122304 q = 1) : d2071 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d2072 q = 1) (hb : d142665 q = 1) : d146089 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d2072, d142665, d146089, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d2072, d142665, d146089, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  exact h2 p ha hb
theorem andIntro26595 (p : Pattern) (ha : d11918 p = 1) (hb : d142666 p = 1) : d146096 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d142666 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d11909 q = 1) (hb : d142666 q = 1) : d146086 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d11909, d142666, d146086, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26593 q ha hb
    | true =>
      simp only [d11909, d142666, d146086, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d11910 q = 1) (hb : d142666 q = 1) : d146087 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d11910, d146087, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11910, d146087, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d11911 q = 1) (hb : d142666 q = 1) : d146088 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d11911, d146088, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11911, d146088, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d11912 q = 1) (hb : d142666 q = 1) : d146090 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d11912, d142666, d146090, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26594 q ha hb
    | true =>
      simp only [d11912, d142666, d146090, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h6 (q : Pattern) (ha : d11913 q = 1) (hb : d142666 q = 1) : d146091 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d11913, d146091, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11913, d146091, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d11914 q = 1) (hb : d142666 q = 1) : d146092 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d11914, d146092, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11914, d146092, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d11915 q = 1) (hb : d142666 q = 1) : d146093 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d11915, d146093, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d11915, d146093, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d11916 q = 1) (hb : d142666 q = 1) : d146094 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d11916, d146094, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d11916, d146094, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d11917 q = 1) (hb : d142666 q = 1) : d146095 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d11917, d146095, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d11917, d146095, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d11918 q = 1) (hb : d142666 q = 1) : d146096 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d11918, d146096, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d11918, d146096, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h11 p ha hb
theorem andIntro26596 (p : Pattern) (ha : d11922 p = 1) (hb : d142666 p = 1) : d146100 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d142666 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d11912 q = 1) (hb : d142666 q = 1) : d146090 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d11912, d142666, d146090, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26594 q ha hb
    | true =>
      simp only [d11912, d142666, d146090, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d11913 q = 1) (hb : d142666 q = 1) : d146091 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d11913, d146091, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11913, d146091, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d11914 q = 1) (hb : d142666 q = 1) : d146092 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d11914, d146092, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11914, d146092, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d11916 q = 1) (hb : d142666 q = 1) : d146094 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d11916, d146094, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d11916, d146094, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d11921 q = 1) (hb : d142666 q = 1) : d146099 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d11921, d146099, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d11921, d146099, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d11922 q = 1) (hb : d142666 q = 1) : d146100 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d11922, d146100, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d11922, d146100, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h7 p ha hb
theorem andIntro26597 (p : Pattern) (ha : d11928 p = 1) (hb : d142666 p = 1) : d146106 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d142666 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d11919 q = 1) (hb : d142666 q = 1) : d146097 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d11919, d146097, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26595 q ha hb
    | true =>
      simp only [d11919, d146097, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d11920 q = 1) (hb : d142666 q = 1) : d146098 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d11920, d146098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11920, d146098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d11923 q = 1) (hb : d142666 q = 1) : d146101 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d11923, d146101, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26596 q ha hb
    | true =>
      simp only [d11923, d146101, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d11924 q = 1) (hb : d142666 q = 1) : d146102 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d11924, d146102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11924, d146102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d11925 q = 1) (hb : d142666 q = 1) : d146103 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d11925, d146103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d11925, d146103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d11926 q = 1) (hb : d142666 q = 1) : d146104 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d11926, d146104, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d11926, d146104, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d11927 q = 1) (hb : d142666 q = 1) : d146105 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d11927, d146105, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d11927, d146105, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d11928 q = 1) (hb : d142666 q = 1) : d146106 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d11928, d146106, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11928, d146106, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro26598 (p : Pattern) (ha : d11932 p = 1) (hb : d142666 p = 1) : d146110 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d142666 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d11923 q = 1) (hb : d142666 q = 1) : d146101 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d11923, d146101, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26596 q ha hb
    | true =>
      simp only [d11923, d146101, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d11924 q = 1) (hb : d142666 q = 1) : d146102 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d11924, d146102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11924, d146102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d11929 q = 1) (hb : d142666 q = 1) : d146107 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d11929, d146107, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d11929, d146107, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d11930 q = 1) (hb : d142666 q = 1) : d146108 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d11930, d146108, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d11930, d146108, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d11931 q = 1) (hb : d142666 q = 1) : d146109 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d11931, d146109, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d11931, d146109, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d11932 q = 1) (hb : d142666 q = 1) : d146110 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d11932, d146110, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11932, d146110, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro26599 (p : Pattern) (ha : d11938 p = 1) (hb : d142666 p = 1) : d146116 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d142666 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d11933 q = 1) (hb : d142666 q = 1) : d146111 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d11933, d146111, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26597 q ha hb
    | true =>
      simp only [d11933, d146111, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26598 q ha hb
  have h2 (q : Pattern) (ha : d11934 q = 1) (hb : d142666 q = 1) : d146112 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d11934, d146112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11934, d146112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d11935 q = 1) (hb : d142666 q = 1) : d146113 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d11935, d146113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d11935, d146113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d11936 q = 1) (hb : d142666 q = 1) : d146114 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d11936, d146114, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11936, d146114, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d11937 q = 1) (hb : d142666 q = 1) : d146115 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d11937, d146115, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11937, d146115, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d11938 q = 1) (hb : d142666 q = 1) : d146116 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d11938, d146116, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11938, d146116, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro26600 (p : Pattern) (ha : d11941 p = 1) (hb : d142666 p = 1) : d146119 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d142666 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d11919 q = 1) (hb : d142666 q = 1) : d146097 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d11919, d146097, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26595 q ha hb
    | true =>
      simp only [d11919, d146097, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d11920 q = 1) (hb : d142666 q = 1) : d146098 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d11920, d146098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11920, d146098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d11923 q = 1) (hb : d142666 q = 1) : d146101 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d11923, d146101, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26596 q ha hb
    | true =>
      simp only [d11923, d146101, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d11924 q = 1) (hb : d142666 q = 1) : d146102 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d11924, d146102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11924, d146102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d11925 q = 1) (hb : d142666 q = 1) : d146103 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d11925, d146103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d11925, d146103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d11926 q = 1) (hb : d142666 q = 1) : d146104 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d11926, d146104, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d11926, d146104, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d11927 q = 1) (hb : d142666 q = 1) : d146105 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d11927, d146105, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d11927, d146105, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d11941 q = 1) (hb : d142666 q = 1) : d146119 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d11941, d146119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d11941, d146119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro26601 (p : Pattern) (ha : d11942 p = 1) (hb : d142666 p = 1) : d146120 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d142666 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d11923 q = 1) (hb : d142666 q = 1) : d146101 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d11923, d146101, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26596 q ha hb
    | true =>
      simp only [d11923, d146101, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d11924 q = 1) (hb : d142666 q = 1) : d146102 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d11924, d146102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11924, d146102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d11929 q = 1) (hb : d142666 q = 1) : d146107 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d11929, d146107, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d11929, d146107, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d11930 q = 1) (hb : d142666 q = 1) : d146108 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d11930, d146108, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d11930, d146108, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d11931 q = 1) (hb : d142666 q = 1) : d146109 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d11931, d146109, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d11931, d146109, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d11942 q = 1) (hb : d142666 q = 1) : d146120 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d11942, d146120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d11942, d146120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro26602 (p : Pattern) (ha : d11948 p = 1) (hb : d142666 p = 1) : d146126 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d142666 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d11933 q = 1) (hb : d142666 q = 1) : d146111 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d11933, d146111, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26597 q ha hb
    | true =>
      simp only [d11933, d146111, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26598 q ha hb
  have h2 (q : Pattern) (ha : d11934 q = 1) (hb : d142666 q = 1) : d146112 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d11934, d146112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11934, d146112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d11935 q = 1) (hb : d142666 q = 1) : d146113 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d11935, d146113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d11935, d146113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d11936 q = 1) (hb : d142666 q = 1) : d146114 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d11936, d146114, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11936, d146114, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d11937 q = 1) (hb : d142666 q = 1) : d146115 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d11937, d146115, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11937, d146115, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d11943 q = 1) (hb : d142666 q = 1) : d146121 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d11943, d146121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26600 q ha hb
    | true =>
      simp only [d11943, d146121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26601 q ha hb
  have h7 (q : Pattern) (ha : d11944 q = 1) (hb : d142666 q = 1) : d146122 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d11944, d146122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11944, d146122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d11945 q = 1) (hb : d142666 q = 1) : d146123 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d11945, d146123, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d11945, d146123, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d11946 q = 1) (hb : d142666 q = 1) : d146124 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d11946, d146124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11946, d146124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d11947 q = 1) (hb : d142666 q = 1) : d146125 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d11947, d146125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11947, d146125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d11948 q = 1) (hb : d142666 q = 1) : d146126 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d11948, d146126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d11948, d146126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro26603 (p : Pattern) (ha : d12056 p = 1) (hb : d142666 p = 1) : d146208 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d142666 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d11933 q = 1) (hb : d142666 q = 1) : d146111 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d11933, d146111, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26597 q ha hb
    | true =>
      simp only [d11933, d146111, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26598 q ha hb
  have h2 (q : Pattern) (ha : d11934 q = 1) (hb : d142666 q = 1) : d146112 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d11934, d146112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11934, d146112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d11935 q = 1) (hb : d142666 q = 1) : d146113 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d11935, d146113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d11935, d146113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d11936 q = 1) (hb : d142666 q = 1) : d146114 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d11936, d146114, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11936, d146114, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d11937 q = 1) (hb : d142666 q = 1) : d146115 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d11937, d146115, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11937, d146115, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d12051 q = 1) (hb : d142666 q = 1) : d146203 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d12051, d146203, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26598 q ha hb
    | true =>
      simp only [d12051, d146203, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d12052 q = 1) (hb : d142666 q = 1) : d146204 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d12052, d146204, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12052, d146204, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d12053 q = 1) (hb : d142666 q = 1) : d146205 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d12053, d146205, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d12053, d146205, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d12054 q = 1) (hb : d142666 q = 1) : d146206 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d12054, d146206, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12054, d146206, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d12055 q = 1) (hb : d142666 q = 1) : d146207 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d12055, d146207, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12055, d146207, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d12056 q = 1) (hb : d142666 q = 1) : d146208 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d12056, d146208, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d12056, d146208, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro26604 (p : Pattern) (ha : d12062 p = 1) (hb : d142666 p = 1) : d146214 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d142666 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12051 q = 1) (hb : d142666 q = 1) : d146203 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d12051, d146203, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26598 q ha hb
    | true =>
      simp only [d12051, d146203, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d12052 q = 1) (hb : d142666 q = 1) : d146204 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d12052, d146204, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12052, d146204, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d12053 q = 1) (hb : d142666 q = 1) : d146205 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d12053, d146205, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d12053, d146205, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d12054 q = 1) (hb : d142666 q = 1) : d146206 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d12054, d146206, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12054, d146206, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d12055 q = 1) (hb : d142666 q = 1) : d146207 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d12055, d146207, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12055, d146207, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d12057 q = 1) (hb : d142666 q = 1) : d146209 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d12057, d146209, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26601 q ha hb
    | true =>
      simp only [d12057, d146209, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d12058 q = 1) (hb : d142666 q = 1) : d146210 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d12058, d146210, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12058, d146210, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d12059 q = 1) (hb : d142666 q = 1) : d146211 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d12059, d146211, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d12059, d146211, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d12060 q = 1) (hb : d142666 q = 1) : d146212 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d12060, d146212, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12060, d146212, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d12061 q = 1) (hb : d142666 q = 1) : d146213 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d12061, d146213, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12061, d146213, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d12062 q = 1) (hb : d142666 q = 1) : d146214 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d12062, d146214, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d12062, d146214, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro26605 (p : Pattern) (ha : d12071 p = 1) (hb : d142666 p = 1) : d146223 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d142666 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12057 q = 1) (hb : d142666 q = 1) : d146209 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d12057, d146209, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26601 q ha hb
    | true =>
      simp only [d12057, d146209, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d12058 q = 1) (hb : d142666 q = 1) : d146210 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d12058, d146210, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12058, d146210, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d12059 q = 1) (hb : d142666 q = 1) : d146211 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d12059, d146211, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d12059, d146211, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d12060 q = 1) (hb : d142666 q = 1) : d146212 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d12060, d146212, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12060, d146212, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d12061 q = 1) (hb : d142666 q = 1) : d146213 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d12061, d146213, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12061, d146213, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d12071 q = 1) (hb : d142666 q = 1) : d146223 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d12071, d146223, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12071, d146223, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro26606 (p : Pattern) (ha : d2356 p = 1) (hb : d142665 p = 1) : d146238 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d2350 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d2355 q = 1) (hb : d122304 q = 1) : d2355 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d2356 q = 1) (hb : d142665 q = 1) : d146238 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d2356, d142665, d146238, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d2356, d142665, d146238, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  exact h2 p ha hb
theorem andIntro26607 (p : Pattern) (ha : d12102 p = 1) (hb : d142666 p = 1) : d146257 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d142666 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d12084 q = 1) (hb : d142666 q = 1) : d146239 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d12084, d142666, d146239, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26606 q ha hb
    | true =>
      simp only [d12084, d142666, d146239, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d12085 q = 1) (hb : d142666 q = 1) : d146240 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d12085, d146240, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12085, d146240, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d12086 q = 1) (hb : d142666 q = 1) : d146241 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d12086, d146241, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12086, d146241, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d12092 q = 1) (hb : d142666 q = 1) : d146247 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d12092, d146247, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d12092, d146247, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d12101 q = 1) (hb : d142666 q = 1) : d146256 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d12101, d146256, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d12101, d146256, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d12102 q = 1) (hb : d142666 q = 1) : d146257 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d12102, d146257, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d12102, d146257, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h7 p ha hb
theorem andIntro26608 (p : Pattern) (ha : d12158 p = 1) (hb : d142666 p = 1) : d146289 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d142666 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12103 q = 1) (hb : d142666 q = 1) : d146258 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d12103, d146258, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26607 q ha hb
    | true =>
      simp only [d12103, d146258, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d12104 q = 1) (hb : d142666 q = 1) : d146259 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d12104, d146259, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12104, d146259, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d12155 q = 1) (hb : d142666 q = 1) : d146286 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d12155, d146286, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d12155, d146286, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d12156 q = 1) (hb : d142666 q = 1) : d146287 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d12156, d146287, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d12156, d146287, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d12157 q = 1) (hb : d142666 q = 1) : d146288 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d12157, d146288, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d12157, d146288, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d12158 q = 1) (hb : d142666 q = 1) : d146289 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d12158, d146289, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d12158, d146289, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro26609 (p : Pattern) (ha : d12164 p = 1) (hb : d142666 p = 1) : d146295 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d142666 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12159 q = 1) (hb : d142666 q = 1) : d146290 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d12159, d146290, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26608 q ha hb
    | true =>
      simp only [d12159, d146290, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d12160 q = 1) (hb : d142666 q = 1) : d146291 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d12160, d146291, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12160, d146291, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d12161 q = 1) (hb : d142666 q = 1) : d146292 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d12161, d146292, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d12161, d146292, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d12162 q = 1) (hb : d142666 q = 1) : d146293 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d12162, d146293, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12162, d146293, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d12163 q = 1) (hb : d142666 q = 1) : d146294 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d12163, d146294, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12163, d146294, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d12164 q = 1) (hb : d142666 q = 1) : d146295 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d12164, d146295, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12164, d146295, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro26610 (p : Pattern) (ha : d11953 p = 1) (hb : d142666 p = 1) : d146131 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d142666 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d11919 q = 1) (hb : d142666 q = 1) : d146097 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d11919, d146097, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26595 q ha hb
    | true =>
      simp only [d11919, d146097, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d11920 q = 1) (hb : d142666 q = 1) : d146098 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d11920, d146098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11920, d146098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d11923 q = 1) (hb : d142666 q = 1) : d146101 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d11923, d146101, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26596 q ha hb
    | true =>
      simp only [d11923, d146101, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d11924 q = 1) (hb : d142666 q = 1) : d146102 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d11924, d146102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11924, d146102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d11925 q = 1) (hb : d142666 q = 1) : d146103 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d11925, d146103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d11925, d146103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d11926 q = 1) (hb : d142666 q = 1) : d146104 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d11926, d146104, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d11926, d146104, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d11952 q = 1) (hb : d142666 q = 1) : d146130 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d11952, d146130, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11952, d146130, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d11953 q = 1) (hb : d142666 q = 1) : d146131 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d11953, d146131, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11953, d146131, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro26611 (p : Pattern) (ha : d11955 p = 1) (hb : d142666 p = 1) : d146133 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d142666 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d11923 q = 1) (hb : d142666 q = 1) : d146101 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d11923, d146101, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26596 q ha hb
    | true =>
      simp only [d11923, d146101, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d11924 q = 1) (hb : d142666 q = 1) : d146102 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d11924, d146102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11924, d146102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d11929 q = 1) (hb : d142666 q = 1) : d146107 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d11929, d146107, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d11929, d146107, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d11930 q = 1) (hb : d142666 q = 1) : d146108 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d11930, d146108, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d11930, d146108, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d11954 q = 1) (hb : d142666 q = 1) : d146132 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d11954, d146132, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11954, d146132, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d11955 q = 1) (hb : d142666 q = 1) : d146133 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d11955, d146133, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11955, d146133, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro26612 (p : Pattern) (ha : d11962 p = 1) (hb : d142666 p = 1) : d146140 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d142666 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d11919 q = 1) (hb : d142666 q = 1) : d146097 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d11919, d146097, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26595 q ha hb
    | true =>
      simp only [d11919, d146097, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d11920 q = 1) (hb : d142666 q = 1) : d146098 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d11920, d146098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11920, d146098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d11923 q = 1) (hb : d142666 q = 1) : d146101 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d11923, d146101, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26596 q ha hb
    | true =>
      simp only [d11923, d146101, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d11924 q = 1) (hb : d142666 q = 1) : d146102 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d11924, d146102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11924, d146102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d11925 q = 1) (hb : d142666 q = 1) : d146103 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d11925, d146103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d11925, d146103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d11960 q = 1) (hb : d142666 q = 1) : d146138 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d11960, d146138, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11960, d146138, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d11961 q = 1) (hb : d142666 q = 1) : d146139 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d11961, d146139, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d11961, d146139, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d11962 q = 1) (hb : d142666 q = 1) : d146140 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d11962, d146140, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11962, d146140, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro26613 (p : Pattern) (ha : d11965 p = 1) (hb : d142666 p = 1) : d146143 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d142666 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d11923 q = 1) (hb : d142666 q = 1) : d146101 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d11923, d146101, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26596 q ha hb
    | true =>
      simp only [d11923, d146101, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d11924 q = 1) (hb : d142666 q = 1) : d146102 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d11924, d146102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11924, d146102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d11929 q = 1) (hb : d142666 q = 1) : d146107 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d11929, d146107, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d11929, d146107, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d11963 q = 1) (hb : d142666 q = 1) : d146141 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d11963, d146141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11963, d146141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d11964 q = 1) (hb : d142666 q = 1) : d146142 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d11964, d146142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d11964, d146142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d11965 q = 1) (hb : d142666 q = 1) : d146143 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d11965, d146143, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11965, d146143, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro26614 (p : Pattern) (ha : d2149 p = 1) (hb : d142665 p = 1) : d146147 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d2148 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1 q = 1) (hb : d2038 q = 1) : d2038 q = 1 := by
    exact hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d2056 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d2057 q = 1) (hb : d122304 q = 1) : d15544 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d2057, d122304, d15544, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d2057, d122304, d15544, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d2149 q = 1) (hb : d142665 q = 1) : d146147 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d2149, d142665, d146147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d2149, d142665, d146147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  exact h4 p ha hb
theorem andIntro26615 (p : Pattern) (ha : d11974 p = 1) (hb : d142666 p = 1) : d146153 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d142666 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d11969 q = 1) (hb : d142666 q = 1) : d146148 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d11969, d142666, d146148, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26614 q ha hb
    | true =>
      simp only [d11969, d142666, d146148, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d11970 q = 1) (hb : d142666 q = 1) : d146149 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d11970, d146149, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11970, d146149, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d11971 q = 1) (hb : d142666 q = 1) : d146150 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d11971, d146150, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11971, d146150, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d11909 q = 1) (hb : d142666 q = 1) : d146086 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d11909, d142666, d146086, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26593 q ha hb
    | true =>
      simp only [d11909, d142666, d146086, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h6 (q : Pattern) (ha : d11910 q = 1) (hb : d142666 q = 1) : d146087 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d11910, d146087, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11910, d146087, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d11911 q = 1) (hb : d142666 q = 1) : d146088 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d11911, d146088, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11911, d146088, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d11972 q = 1) (hb : d142666 q = 1) : d146151 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d11972, d146151, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d11972, d146151, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d11912 q = 1) (hb : d142666 q = 1) : d146090 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d11912, d142666, d146090, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26594 q ha hb
    | true =>
      simp only [d11912, d142666, d146090, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h10 (q : Pattern) (ha : d11913 q = 1) (hb : d142666 q = 1) : d146091 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d11913, d146091, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11913, d146091, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d11914 q = 1) (hb : d142666 q = 1) : d146092 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d11914, d146092, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11914, d146092, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d11915 q = 1) (hb : d142666 q = 1) : d146093 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d11915, d146093, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d11915, d146093, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d11973 q = 1) (hb : d142666 q = 1) : d146152 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d11973, d146152, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d11973, d146152, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d11974 q = 1) (hb : d142666 q = 1) : d146153 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d11974, d146153, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d11974, d146153, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h14 p ha hb
theorem andIntro26616 (p : Pattern) (ha : d11980 p = 1) (hb : d142666 p = 1) : d146159 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d142666 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d11975 q = 1) (hb : d142666 q = 1) : d146154 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d11975, d146154, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26615 q ha hb
    | true =>
      simp only [d11975, d146154, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d11976 q = 1) (hb : d142666 q = 1) : d146155 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d11976, d146155, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11976, d146155, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d11919 q = 1) (hb : d142666 q = 1) : d146097 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d11919, d146097, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26595 q ha hb
    | true =>
      simp only [d11919, d146097, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d11920 q = 1) (hb : d142666 q = 1) : d146098 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d11920, d146098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11920, d146098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d11977 q = 1) (hb : d142666 q = 1) : d146156 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d11977, d146156, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d11977, d146156, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d11978 q = 1) (hb : d142666 q = 1) : d146157 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d11978, d146157, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d11978, d146157, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d11979 q = 1) (hb : d142666 q = 1) : d146158 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d11979, d146158, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d11979, d146158, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d11980 q = 1) (hb : d142666 q = 1) : d146159 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d11980, d146159, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11980, d146159, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro26617 (p : Pattern) (ha : d5726 p = 1) (hb : d142665 p = 1) : d146162 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d2069 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d5725 q = 1) (hb : d122304 q = 1) : d5725 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d5726 q = 1) (hb : d142665 q = 1) : d146162 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d5726, d142665, d146162, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d5726, d142665, d146162, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  exact h2 p ha hb
theorem andIntro26618 (p : Pattern) (ha : d12013 p = 1) (hb : d142666 p = 1) : d146168 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d142666 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d11909 q = 1) (hb : d142666 q = 1) : d146086 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d11909, d142666, d146086, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26593 q ha hb
    | true =>
      simp only [d11909, d142666, d146086, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d11910 q = 1) (hb : d142666 q = 1) : d146087 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d11910, d146087, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11910, d146087, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d11911 q = 1) (hb : d142666 q = 1) : d146088 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d11911, d146088, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11911, d146088, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d11912 q = 1) (hb : d142666 q = 1) : d146090 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d11912, d142666, d146090, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26594 q ha hb
    | true =>
      simp only [d11912, d142666, d146090, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h6 (q : Pattern) (ha : d11913 q = 1) (hb : d142666 q = 1) : d146091 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d11913, d146091, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11913, d146091, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d11914 q = 1) (hb : d142666 q = 1) : d146092 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d11914, d146092, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11914, d146092, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d11915 q = 1) (hb : d142666 q = 1) : d146093 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d11915, d146093, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d11915, d146093, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d12008 q = 1) (hb : d142666 q = 1) : d146163 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d12008, d142666, d146163, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26617 q ha hb
    | true =>
      simp only [d12008, d142666, d146163, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h10 (q : Pattern) (ha : d12009 q = 1) (hb : d142666 q = 1) : d146164 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d12009, d146164, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12009, d146164, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d12010 q = 1) (hb : d142666 q = 1) : d146165 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d12010, d146165, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12010, d146165, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d12011 q = 1) (hb : d142666 q = 1) : d146166 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d12011, d146166, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d12011, d146166, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d12012 q = 1) (hb : d142666 q = 1) : d146167 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d12012, d146167, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d12012, d146167, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d12013 q = 1) (hb : d142666 q = 1) : d146168 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d12013, d146168, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d12013, d146168, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h14 p ha hb
theorem andIntro26619 (p : Pattern) (ha : d12019 p = 1) (hb : d142666 p = 1) : d146174 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d142666 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12014 q = 1) (hb : d142666 q = 1) : d146169 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d12014, d146169, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26618 q ha hb
    | true =>
      simp only [d12014, d146169, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d12015 q = 1) (hb : d142666 q = 1) : d146170 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d12015, d146170, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12015, d146170, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d12016 q = 1) (hb : d142666 q = 1) : d146171 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d12016, d146171, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d12016, d146171, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d12017 q = 1) (hb : d142666 q = 1) : d146172 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d12017, d146172, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d12017, d146172, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d12018 q = 1) (hb : d142666 q = 1) : d146173 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d12018, d146173, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d12018, d146173, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d12019 q = 1) (hb : d142666 q = 1) : d146174 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d12019, d146174, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12019, d146174, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro26620 (p : Pattern) (ha : d109027 p = 1) (hb : d142666 p = 1) : d146180 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d142666 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d11956 q = 1) (hb : d142666 q = 1) : d146134 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d11956, d146134, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26610 q ha hb
    | true =>
      simp only [d11956, d146134, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26611 q ha hb
  have h2 (q : Pattern) (ha : d11957 q = 1) (hb : d142666 q = 1) : d146135 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d11957, d146135, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11957, d146135, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d11958 q = 1) (hb : d142666 q = 1) : d146136 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d11958, d146136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d11958, d146136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d11959 q = 1) (hb : d142666 q = 1) : d146137 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d11959, d146137, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11959, d146137, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d11966 q = 1) (hb : d142666 q = 1) : d146144 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d11966, d146144, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26612 q ha hb
    | true =>
      simp only [d11966, d146144, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26613 q ha hb
  have h6 (q : Pattern) (ha : d11967 q = 1) (hb : d142666 q = 1) : d146145 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d11967, d146145, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11967, d146145, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d11968 q = 1) (hb : d142666 q = 1) : d146146 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d11968, d146146, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d11968, d146146, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d11981 q = 1) (hb : d142666 q = 1) : d146160 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d11981, d146160, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26616 q ha hb
    | true =>
      simp only [d11981, d146160, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26597 q ha hb
  have h9 (q : Pattern) (ha : d109023 q = 1) (hb : d142666 q = 1) : d146161 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d109023, d146161, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d109023, d146161, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d12020 q = 1) (hb : d142666 q = 1) : d146175 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d12020, d146175, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26619 q ha hb
    | true =>
      simp only [d12020, d146175, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d12021 q = 1) (hb : d142666 q = 1) : d146176 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d12021, d146176, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d12021, d146176, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d109024 q = 1) (hb : d142666 q = 1) : d146177 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d109024, d146177, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d109024, d146177, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d109025 q = 1) (hb : d142666 q = 1) : d146178 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d109025, d146178, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d109025, d146178, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d109026 q = 1) (hb : d142666 q = 1) : d146179 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d109026, d146179, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d109026, d146179, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d109027 q = 1) (hb : d142666 q = 1) : d146180 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d109027, d146180, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d109027, d146180, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro26621 (p : Pattern) (ha : d12026 p = 1) (hb : d142666 p = 1) : d146181 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d142666 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d11919 q = 1) (hb : d142666 q = 1) : d146097 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d11919, d146097, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26595 q ha hb
    | true =>
      simp only [d11919, d146097, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d11920 q = 1) (hb : d142666 q = 1) : d146098 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d11920, d146098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11920, d146098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d11923 q = 1) (hb : d142666 q = 1) : d146101 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d11923, d146101, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26596 q ha hb
    | true =>
      simp only [d11923, d146101, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d11924 q = 1) (hb : d142666 q = 1) : d146102 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d11924, d146102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11924, d146102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d11925 q = 1) (hb : d142666 q = 1) : d146103 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d11925, d146103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d11925, d146103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d11926 q = 1) (hb : d142666 q = 1) : d146104 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d11926, d146104, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d11926, d146104, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d11952 q = 1) (hb : d142666 q = 1) : d146130 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d11952, d146130, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11952, d146130, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d12026 q = 1) (hb : d142666 q = 1) : d146181 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d12026, d146181, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d12026, d146181, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro26622 (p : Pattern) (ha : d12027 p = 1) (hb : d142666 p = 1) : d146182 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d142666 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d11923 q = 1) (hb : d142666 q = 1) : d146101 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d11923, d146101, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26596 q ha hb
    | true =>
      simp only [d11923, d146101, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d11924 q = 1) (hb : d142666 q = 1) : d146102 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d11924, d146102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11924, d146102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d11929 q = 1) (hb : d142666 q = 1) : d146107 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d11929, d146107, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d11929, d146107, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d11930 q = 1) (hb : d142666 q = 1) : d146108 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d11930, d146108, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d11930, d146108, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d11954 q = 1) (hb : d142666 q = 1) : d146132 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d11954, d146132, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11954, d146132, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d12027 q = 1) (hb : d142666 q = 1) : d146182 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d12027, d146182, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d12027, d146182, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro26623 (p : Pattern) (ha : d12032 p = 1) (hb : d142666 p = 1) : d146187 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d142666 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d11919 q = 1) (hb : d142666 q = 1) : d146097 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d11919, d146097, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26595 q ha hb
    | true =>
      simp only [d11919, d146097, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d11920 q = 1) (hb : d142666 q = 1) : d146098 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d11920, d146098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11920, d146098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d11923 q = 1) (hb : d142666 q = 1) : d146101 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d11923, d146101, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26596 q ha hb
    | true =>
      simp only [d11923, d146101, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d11924 q = 1) (hb : d142666 q = 1) : d146102 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d11924, d146102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11924, d146102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d11925 q = 1) (hb : d142666 q = 1) : d146103 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d11925, d146103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d11925, d146103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d11960 q = 1) (hb : d142666 q = 1) : d146138 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d11960, d146138, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11960, d146138, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d11961 q = 1) (hb : d142666 q = 1) : d146139 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d11961, d146139, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d11961, d146139, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d12032 q = 1) (hb : d142666 q = 1) : d146187 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d12032, d146187, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d12032, d146187, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro26624 (p : Pattern) (ha : d12033 p = 1) (hb : d142666 p = 1) : d146188 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d142666 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d11923 q = 1) (hb : d142666 q = 1) : d146101 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d11923, d146101, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26596 q ha hb
    | true =>
      simp only [d11923, d146101, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d11924 q = 1) (hb : d142666 q = 1) : d146102 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d11924, d146102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11924, d146102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d11929 q = 1) (hb : d142666 q = 1) : d146107 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d11929, d146107, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d11929, d146107, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d11963 q = 1) (hb : d142666 q = 1) : d146141 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d11963, d146141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11963, d146141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d11964 q = 1) (hb : d142666 q = 1) : d146142 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d11964, d146142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d11964, d146142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d12033 q = 1) (hb : d142666 q = 1) : d146188 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d12033, d146188, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d12033, d146188, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro26625 (p : Pattern) (ha : d12037 p = 1) (hb : d142666 p = 1) : d146192 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d142666 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d11975 q = 1) (hb : d142666 q = 1) : d146154 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d11975, d146154, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26615 q ha hb
    | true =>
      simp only [d11975, d146154, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d11976 q = 1) (hb : d142666 q = 1) : d146155 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d11976, d146155, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11976, d146155, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d11919 q = 1) (hb : d142666 q = 1) : d146097 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d11919, d146097, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26595 q ha hb
    | true =>
      simp only [d11919, d146097, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d11920 q = 1) (hb : d142666 q = 1) : d146098 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d11920, d146098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11920, d146098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d11977 q = 1) (hb : d142666 q = 1) : d146156 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d11977, d146156, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d11977, d146156, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d11978 q = 1) (hb : d142666 q = 1) : d146157 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d11978, d146157, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d11978, d146157, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d11979 q = 1) (hb : d142666 q = 1) : d146158 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d11979, d146158, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d11979, d146158, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d12037 q = 1) (hb : d142666 q = 1) : d146192 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d12037, d146192, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d12037, d146192, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro26626 (p : Pattern) (ha : d12043 p = 1) (hb : d142666 p = 1) : d146195 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d142666 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12014 q = 1) (hb : d142666 q = 1) : d146169 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d12014, d146169, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26618 q ha hb
    | true =>
      simp only [d12014, d146169, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d12015 q = 1) (hb : d142666 q = 1) : d146170 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d12015, d146170, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12015, d146170, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d12016 q = 1) (hb : d142666 q = 1) : d146171 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d12016, d146171, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d12016, d146171, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d12017 q = 1) (hb : d142666 q = 1) : d146172 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d12017, d146172, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d12017, d146172, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d12018 q = 1) (hb : d142666 q = 1) : d146173 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d12018, d146173, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d12018, d146173, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d12043 q = 1) (hb : d142666 q = 1) : d146195 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d12043, d146195, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d12043, d146195, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro26627 (p : Pattern) (ha : d109032 p = 1) (hb : d142666 p = 1) : d146201 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d142666 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d11956 q = 1) (hb : d142666 q = 1) : d146134 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d11956, d146134, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26610 q ha hb
    | true =>
      simp only [d11956, d146134, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26611 q ha hb
  have h2 (q : Pattern) (ha : d11957 q = 1) (hb : d142666 q = 1) : d146135 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d11957, d146135, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11957, d146135, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d11958 q = 1) (hb : d142666 q = 1) : d146136 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d11958, d146136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d11958, d146136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d11959 q = 1) (hb : d142666 q = 1) : d146137 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d11959, d146137, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11959, d146137, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d11966 q = 1) (hb : d142666 q = 1) : d146144 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d11966, d146144, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26612 q ha hb
    | true =>
      simp only [d11966, d146144, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26613 q ha hb
  have h6 (q : Pattern) (ha : d11967 q = 1) (hb : d142666 q = 1) : d146145 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d11967, d146145, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11967, d146145, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d11968 q = 1) (hb : d142666 q = 1) : d146146 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d11968, d146146, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d11968, d146146, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d11981 q = 1) (hb : d142666 q = 1) : d146160 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d11981, d146160, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26616 q ha hb
    | true =>
      simp only [d11981, d146160, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26597 q ha hb
  have h9 (q : Pattern) (ha : d109023 q = 1) (hb : d142666 q = 1) : d146161 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d109023, d146161, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d109023, d146161, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d12020 q = 1) (hb : d142666 q = 1) : d146175 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d12020, d146175, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26619 q ha hb
    | true =>
      simp only [d12020, d146175, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d12021 q = 1) (hb : d142666 q = 1) : d146176 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d12021, d146176, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d12021, d146176, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d109024 q = 1) (hb : d142666 q = 1) : d146177 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d109024, d146177, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d109024, d146177, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d109025 q = 1) (hb : d142666 q = 1) : d146178 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d109025, d146178, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d109025, d146178, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d109026 q = 1) (hb : d142666 q = 1) : d146179 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d109026, d146179, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d109026, d146179, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d12028 q = 1) (hb : d142666 q = 1) : d146183 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d12028, d146183, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26621 q ha hb
    | true =>
      simp only [d12028, d146183, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26622 q ha hb
  have h16 (q : Pattern) (ha : d12029 q = 1) (hb : d142666 q = 1) : d146184 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d12029, d146184, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12029, d146184, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d12030 q = 1) (hb : d142666 q = 1) : d146185 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d12030, d146185, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d12030, d146185, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h18 (q : Pattern) (ha : d12031 q = 1) (hb : d142666 q = 1) : d146186 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d12031, d146186, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12031, d146186, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d12034 q = 1) (hb : d142666 q = 1) : d146189 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d12034, d146189, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26623 q ha hb
    | true =>
      simp only [d12034, d146189, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26624 q ha hb
  have h20 (q : Pattern) (ha : d12035 q = 1) (hb : d142666 q = 1) : d146190 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d12035, d146190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12035, d146190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
  have h21 (q : Pattern) (ha : d12036 q = 1) (hb : d142666 q = 1) : d146191 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d12036, d146191, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d12036, d146191, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h22 (q : Pattern) (ha : d12038 q = 1) (hb : d142666 q = 1) : d146193 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d12038, d146193, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26625 q ha hb
    | true =>
      simp only [d12038, d146193, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26600 q ha hb
  have h23 (q : Pattern) (ha : d109028 q = 1) (hb : d142666 q = 1) : d146194 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d109028, d146194, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
    | true =>
      simp only [d109028, d146194, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h24 (q : Pattern) (ha : d12044 q = 1) (hb : d142666 q = 1) : d146196 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d12044, d146196, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26626 q ha hb
    | true =>
      simp only [d12044, d146196, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h25 (q : Pattern) (ha : d12045 q = 1) (hb : d142666 q = 1) : d146197 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d12045, d146197, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q ha hb
    | true =>
      simp only [d12045, d146197, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h26 (q : Pattern) (ha : d109029 q = 1) (hb : d142666 q = 1) : d146198 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d109029, d146198, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
    | true =>
      simp only [d109029, d146198, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q ha hb
  have h27 (q : Pattern) (ha : d109030 q = 1) (hb : d142666 q = 1) : d146199 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d109030, d146199, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d109030, d146199, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h26 q ha hb
  have h28 (q : Pattern) (ha : d109031 q = 1) (hb : d142666 q = 1) : d146200 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d109031, d146200, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d109031, d146200, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h27 q ha hb
  have h29 (q : Pattern) (ha : d109032 q = 1) (hb : d142666 q = 1) : d146201 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d109032, d146201, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d109032, d146201, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h28 q ha hb
  exact h29 p ha hb
theorem andIntro26628 (p : Pattern) (ha : d109039 p = 1) (hb : d142666 p = 1) : d146221 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d142666 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12038 q = 1) (hb : d142666 q = 1) : d146193 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d12038, d146193, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26625 q ha hb
    | true =>
      simp only [d12038, d146193, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26600 q ha hb
  have h2 (q : Pattern) (ha : d109028 q = 1) (hb : d142666 q = 1) : d146194 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d109028, d146194, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d109028, d146194, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d12044 q = 1) (hb : d142666 q = 1) : d146196 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d12044, d146196, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26626 q ha hb
    | true =>
      simp only [d12044, d146196, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d12045 q = 1) (hb : d142666 q = 1) : d146197 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d12045, d146197, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d12045, d146197, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d109029 q = 1) (hb : d142666 q = 1) : d146198 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d109029, d146198, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d109029, d146198, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d109037 q = 1) (hb : d142666 q = 1) : d146219 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d109037, d146219, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d109037, d146219, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d109038 q = 1) (hb : d142666 q = 1) : d146220 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d109038, d146220, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d109038, d146220, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d109039 q = 1) (hb : d142666 q = 1) : d146221 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d109039, d146221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d109039, d146221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro26629 (p : Pattern) (ha : d2345 p = 1) (hb : d142665 p = 1) : d146229 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d2339 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1 q = 1) (hb : d2338 q = 1) : d2338 q = 1 := by
    exact hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d2343 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d2344 q = 1) (hb : d122304 q = 1) : d15769 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d2344, d122304, d15769, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d2344, d122304, d15769, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d2345 q = 1) (hb : d142665 q = 1) : d146229 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d2345, d142665, d146229, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d2345, d142665, d146229, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  exact h4 p ha hb
theorem andIntro26630 (p : Pattern) (ha : d2351 p = 1) (hb : d142665 p = 1) : d146233 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d2344 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1 q = 1) (hb : d2343 q = 1) : d2343 q = 1 := by
    exact hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d2349 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d2350 q = 1) (hb : d122304 q = 1) : d15785 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d2350, d122304, d15785, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d2350, d122304, d15785, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d2351 q = 1) (hb : d142665 q = 1) : d146233 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d2351, d142665, d146233, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d2351, d142665, d146233, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  exact h4 p ha hb
theorem andIntro26631 (p : Pattern) (ha : d12089 p = 1) (hb : d142666 p = 1) : d146244 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d142666 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d12077 q = 1) (hb : d142666 q = 1) : d146230 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d12077, d142666, d146230, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26629 q ha hb
    | true =>
      simp only [d12077, d142666, d146230, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d12078 q = 1) (hb : d142666 q = 1) : d146231 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d12078, d146231, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12078, d146231, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d12079 q = 1) (hb : d142666 q = 1) : d146232 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d12079, d146232, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12079, d146232, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d12080 q = 1) (hb : d142666 q = 1) : d146234 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d12080, d142666, d146234, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26630 q ha hb
    | true =>
      simp only [d12080, d142666, d146234, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h6 (q : Pattern) (ha : d12081 q = 1) (hb : d142666 q = 1) : d146235 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d12081, d146235, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12081, d146235, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d12082 q = 1) (hb : d142666 q = 1) : d146236 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d12082, d146236, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12082, d146236, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d12083 q = 1) (hb : d142666 q = 1) : d146237 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d12083, d146237, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d12083, d146237, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d12084 q = 1) (hb : d142666 q = 1) : d146239 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d12084, d142666, d146239, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26606 q ha hb
    | true =>
      simp only [d12084, d142666, d146239, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h10 (q : Pattern) (ha : d12085 q = 1) (hb : d142666 q = 1) : d146240 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d12085, d146240, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12085, d146240, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d12086 q = 1) (hb : d142666 q = 1) : d146241 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d12086, d146241, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12086, d146241, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d12087 q = 1) (hb : d142666 q = 1) : d146242 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d12087, d146242, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d12087, d146242, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d12088 q = 1) (hb : d142666 q = 1) : d146243 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d12088, d146243, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d12088, d146243, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d12089 q = 1) (hb : d142666 q = 1) : d146244 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d12089, d146244, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d12089, d146244, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h14 p ha hb
theorem andIntro26632 (p : Pattern) (ha : d12094 p = 1) (hb : d142666 p = 1) : d146249 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d142666 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d12080 q = 1) (hb : d142666 q = 1) : d146234 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d12080, d142666, d146234, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26630 q ha hb
    | true =>
      simp only [d12080, d142666, d146234, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d12081 q = 1) (hb : d142666 q = 1) : d146235 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d12081, d146235, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12081, d146235, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d12082 q = 1) (hb : d142666 q = 1) : d146236 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d12082, d146236, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12082, d146236, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d12084 q = 1) (hb : d142666 q = 1) : d146239 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d12084, d142666, d146239, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26606 q ha hb
    | true =>
      simp only [d12084, d142666, d146239, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h6 (q : Pattern) (ha : d12085 q = 1) (hb : d142666 q = 1) : d146240 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d12085, d146240, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12085, d146240, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d12086 q = 1) (hb : d142666 q = 1) : d146241 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d12086, d146241, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12086, d146241, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d12087 q = 1) (hb : d142666 q = 1) : d146242 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d12087, d146242, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d12087, d146242, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d12092 q = 1) (hb : d142666 q = 1) : d146247 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d12092, d146247, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d12092, d146247, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d12093 q = 1) (hb : d142666 q = 1) : d146248 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d12093, d146248, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d12093, d146248, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d12094 q = 1) (hb : d142666 q = 1) : d146249 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d12094, d146249, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d12094, d146249, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h11 p ha hb
theorem andIntro26633 (p : Pattern) (ha : d12100 p = 1) (hb : d142666 p = 1) : d146255 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d142666 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12090 q = 1) (hb : d142666 q = 1) : d146245 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d12090, d146245, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26631 q ha hb
    | true =>
      simp only [d12090, d146245, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d12091 q = 1) (hb : d142666 q = 1) : d146246 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d12091, d146246, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12091, d146246, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d12095 q = 1) (hb : d142666 q = 1) : d146250 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d12095, d146250, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26632 q ha hb
    | true =>
      simp only [d12095, d146250, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d12096 q = 1) (hb : d142666 q = 1) : d146251 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d12096, d146251, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12096, d146251, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d12097 q = 1) (hb : d142666 q = 1) : d146252 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d12097, d146252, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d12097, d146252, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d12098 q = 1) (hb : d142666 q = 1) : d146253 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d12098, d146253, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d12098, d146253, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d12099 q = 1) (hb : d142666 q = 1) : d146254 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d12099, d146254, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d12099, d146254, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d12100 q = 1) (hb : d142666 q = 1) : d146255 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d12100, d146255, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d12100, d146255, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro26634 (p : Pattern) (ha : d12108 p = 1) (hb : d142666 p = 1) : d146263 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d142666 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12095 q = 1) (hb : d142666 q = 1) : d146250 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d12095, d146250, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26632 q ha hb
    | true =>
      simp only [d12095, d146250, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d12096 q = 1) (hb : d142666 q = 1) : d146251 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d12096, d146251, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12096, d146251, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d12103 q = 1) (hb : d142666 q = 1) : d146258 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d12103, d146258, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26607 q ha hb
    | true =>
      simp only [d12103, d146258, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d12104 q = 1) (hb : d142666 q = 1) : d146259 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d12104, d146259, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12104, d146259, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d12105 q = 1) (hb : d142666 q = 1) : d146260 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d12105, d146260, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d12105, d146260, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d12106 q = 1) (hb : d142666 q = 1) : d146261 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d12106, d146261, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d12106, d146261, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d12107 q = 1) (hb : d142666 q = 1) : d146262 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d12107, d146262, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d12107, d146262, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d12108 q = 1) (hb : d142666 q = 1) : d146263 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d12108, d146263, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d12108, d146263, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro26635 (p : Pattern) (ha : d5770 p = 1) (hb : d142665 p = 1) : d146266 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d2350 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d5769 q = 1) (hb : d122304 q = 1) : d5769 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d5770 q = 1) (hb : d142665 q = 1) : d146266 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d5770, d142665, d146266, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d5770, d142665, d146266, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  exact h2 p ha hb
theorem andIntro26636 (p : Pattern) (ha : d12141 p = 1) (hb : d142666 p = 1) : d146272 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d142666 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d12080 q = 1) (hb : d142666 q = 1) : d146234 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d12080, d142666, d146234, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26630 q ha hb
    | true =>
      simp only [d12080, d142666, d146234, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d12081 q = 1) (hb : d142666 q = 1) : d146235 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d12081, d146235, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12081, d146235, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d12082 q = 1) (hb : d142666 q = 1) : d146236 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d12082, d146236, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12082, d146236, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d12084 q = 1) (hb : d142666 q = 1) : d146239 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d12084, d142666, d146239, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26606 q ha hb
    | true =>
      simp only [d12084, d142666, d146239, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h6 (q : Pattern) (ha : d12085 q = 1) (hb : d142666 q = 1) : d146240 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d12085, d146240, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12085, d146240, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d12086 q = 1) (hb : d142666 q = 1) : d146241 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d12086, d146241, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12086, d146241, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d12087 q = 1) (hb : d142666 q = 1) : d146242 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d12087, d146242, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d12087, d146242, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d12136 q = 1) (hb : d142666 q = 1) : d146267 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d12136, d142666, d146267, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26635 q ha hb
    | true =>
      simp only [d12136, d142666, d146267, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h10 (q : Pattern) (ha : d12137 q = 1) (hb : d142666 q = 1) : d146268 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d12137, d146268, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12137, d146268, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d12138 q = 1) (hb : d142666 q = 1) : d146269 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d12138, d146269, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12138, d146269, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d12139 q = 1) (hb : d142666 q = 1) : d146270 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d12139, d146270, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d12139, d146270, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d12140 q = 1) (hb : d142666 q = 1) : d146271 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d12140, d146271, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d12140, d146271, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d12141 q = 1) (hb : d142666 q = 1) : d146272 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d12141, d146272, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d12141, d146272, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h14 p ha hb
theorem andIntro26637 (p : Pattern) (ha : d12147 p = 1) (hb : d142666 p = 1) : d146278 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d142666 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12142 q = 1) (hb : d142666 q = 1) : d146273 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d12142, d146273, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26636 q ha hb
    | true =>
      simp only [d12142, d146273, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d12143 q = 1) (hb : d142666 q = 1) : d146274 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d12143, d146274, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12143, d146274, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d12144 q = 1) (hb : d142666 q = 1) : d146275 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d12144, d146275, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d12144, d146275, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d12145 q = 1) (hb : d142666 q = 1) : d146276 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d12145, d146276, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d12145, d146276, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d12146 q = 1) (hb : d142666 q = 1) : d146277 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d12146, d146277, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d12146, d146277, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d12147 q = 1) (hb : d142666 q = 1) : d146278 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d12147, d146278, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d12147, d146278, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro26638 (p : Pattern) (ha : d109049 p = 1) (hb : d142666 p = 1) : d146284 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d142666 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12109 q = 1) (hb : d142666 q = 1) : d146264 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d12109, d146264, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26633 q ha hb
    | true =>
      simp only [d12109, d146264, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26634 q ha hb
  have h2 (q : Pattern) (ha : d109045 q = 1) (hb : d142666 q = 1) : d146265 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d109045, d146265, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d109045, d146265, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d12148 q = 1) (hb : d142666 q = 1) : d146279 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d12148, d146279, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26637 q ha hb
    | true =>
      simp only [d12148, d146279, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d12149 q = 1) (hb : d142666 q = 1) : d146280 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d12149, d146280, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d12149, d146280, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d109046 q = 1) (hb : d142666 q = 1) : d146281 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d109046, d146281, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d109046, d146281, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d109047 q = 1) (hb : d142666 q = 1) : d146282 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d109047, d146282, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d109047, d146282, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d109048 q = 1) (hb : d142666 q = 1) : d146283 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d109048, d146283, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d109048, d146283, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d109049 q = 1) (hb : d142666 q = 1) : d146284 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d109049, d146284, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d109049, d146284, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro26639 (p : Pattern) (ha : d109055 p = 1) (hb : d142666 p = 1) : d146301 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d142666 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d11939 q = 1) (hb : d142666 q = 1) : d146117 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d11939, d146117, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11939, d146117, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26599 q ha hb
  have h2 (q : Pattern) (ha : d11940 q = 1) (hb : d142666 q = 1) : d146118 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d11940, d146118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d11940, d146118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d11949 q = 1) (hb : d142666 q = 1) : d146127 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d11949, d146127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26599 q ha hb
    | true =>
      simp only [d11949, d146127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26602 q ha hb
  have h4 (q : Pattern) (ha : d11950 q = 1) (hb : d142666 q = 1) : d146128 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d11950, d146128, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d11950, d146128, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d11951 q = 1) (hb : d142666 q = 1) : d146129 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d11951, d146129, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d11951, d146129, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d109033 q = 1) (hb : d142666 q = 1) : d146202 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d109033, d146202, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26620 q ha hb
    | true =>
      simp only [d109033, d146202, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26627 q ha hb
  have h7 (q : Pattern) (ha : d12063 q = 1) (hb : d142666 q = 1) : d146215 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d12063, d146215, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26603 q ha hb
    | true =>
      simp only [d12063, d146215, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26604 q ha hb
  have h8 (q : Pattern) (ha : d109034 q = 1) (hb : d142666 q = 1) : d146216 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d109034, d146216, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d109034, d146216, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d109035 q = 1) (hb : d142666 q = 1) : d146217 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d109035, d146217, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d109035, d146217, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d109036 q = 1) (hb : d142666 q = 1) : d146218 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d109036, d146218, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d109036, d146218, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d109040 q = 1) (hb : d142666 q = 1) : d146222 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d109040, d146222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d109040, d146222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26628 q ha hb
  have h12 (q : Pattern) (ha : d12072 q = 1) (hb : d142666 q = 1) : d146224 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d12072, d146224, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12072, d146224, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26605 q ha hb
  have h13 (q : Pattern) (ha : d109041 q = 1) (hb : d142666 q = 1) : d146225 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d109041, d146225, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d109041, d146225, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d109042 q = 1) (hb : d142666 q = 1) : d146226 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d109042, d146226, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d109042, d146226, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d109043 q = 1) (hb : d142666 q = 1) : d146227 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d109043, d146227, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d109043, d146227, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h16 (q : Pattern) (ha : d109044 q = 1) (hb : d142666 q = 1) : d146228 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d109044, d146228, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d109044, d146228, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d109050 q = 1) (hb : d142666 q = 1) : d146285 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d109050, d146285, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d109050, d146285, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26638 q ha hb
  have h18 (q : Pattern) (ha : d12165 q = 1) (hb : d142666 q = 1) : d146296 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d12165, d146296, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12165, d146296, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26609 q ha hb
  have h19 (q : Pattern) (ha : d109051 q = 1) (hb : d142666 q = 1) : d146297 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d109051, d146297, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d109051, d146297, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d109052 q = 1) (hb : d142666 q = 1) : d146298 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d109052, d146298, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d109052, d146298, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h21 (q : Pattern) (ha : d109053 q = 1) (hb : d142666 q = 1) : d146299 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d109053, d146299, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d109053, d146299, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h22 (q : Pattern) (ha : d109054 q = 1) (hb : d142666 q = 1) : d146300 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d109054, d146300, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d109054, d146300, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h23 (q : Pattern) (ha : d109055 q = 1) (hb : d142666 q = 1) : d146301 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d109055, d146301, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d109055, d146301, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
  exact h23 p ha hb
theorem andIntro26640 (p : Pattern) (ha : d109061 p = 1) (hb : d142666 p = 1) : d146307 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d142666 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d109056 q = 1) (hb : d142666 q = 1) : d146302 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d109056, d146302, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d109056, d146302, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26639 q ha hb
  have h2 (q : Pattern) (ha : d109057 q = 1) (hb : d142666 q = 1) : d146303 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d109057, d146303, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d109057, d146303, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d109058 q = 1) (hb : d142666 q = 1) : d146304 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d109058, d146304, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d109058, d146304, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d109059 q = 1) (hb : d142666 q = 1) : d146305 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d109059, d146305, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d109059, d146305, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d109060 q = 1) (hb : d142666 q = 1) : d146306 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d109060, d146306, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d109060, d146306, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d109061 q = 1) (hb : d142666 q = 1) : d146307 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d109061, d146307, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d109061, d146307, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro26641 (p : Pattern) (ha : d109067 p = 1) (hb : d142666 p = 1) : d146313 p = 1 := by
  have h0 (q : Pattern) (ha : d108896 q = 1) (hb : d142666 q = 1) : d145468 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d108896, d145468, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26408 q ha hb
    | true =>
      simp only [d108896, d145468, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26448 q ha hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d142666 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d108936 q = 1) (hb : d142666 q = 1) : d145630 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d108936, d145630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d108936, d145630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26496 q ha hb
  have h3 (q : Pattern) (ha : d108937 q = 1) (hb : d142666 q = 1) : d145631 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d108937, d145631, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d108937, d145631, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d108977 q = 1) (hb : d142666 q = 1) : d145855 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d108977, d145855, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d108977, d145855, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26544 q ha hb
  have h5 (q : Pattern) (ha : d108978 q = 1) (hb : d142666 q = 1) : d145856 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d108978, d145856, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d108978, d145856, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d108979 q = 1) (hb : d142666 q = 1) : d145857 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d108979, d145857, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d108979, d145857, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d109019 q = 1) (hb : d142666 q = 1) : d146081 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d109019, d146081, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d109019, d146081, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26592 q ha hb
  have h8 (q : Pattern) (ha : d109020 q = 1) (hb : d142666 q = 1) : d146082 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d109020, d146082, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d109020, d146082, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d109021 q = 1) (hb : d142666 q = 1) : d146083 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d109021, d146083, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d109021, d146083, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d109022 q = 1) (hb : d142666 q = 1) : d146084 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d109022, d146084, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d109022, d146084, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d109062 q = 1) (hb : d142666 q = 1) : d146308 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d109062, d146308, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d109062, d146308, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26640 q ha hb
  have h12 (q : Pattern) (ha : d109063 q = 1) (hb : d142666 q = 1) : d146309 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d109063, d146309, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d109063, d146309, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d109064 q = 1) (hb : d142666 q = 1) : d146310 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d109064, d146310, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d109064, d146310, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d109065 q = 1) (hb : d142666 q = 1) : d146311 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d109065, d146311, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d109065, d146311, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d109066 q = 1) (hb : d142666 q = 1) : d146312 q = 1 := by
    cases bit : q 10250 with
    | false =>
      simp only [d109066, d146312, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d109066, d146312, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d109067 q = 1) (hb : d142666 q = 1) : d146313 q = 1 := by
    cases bit : q 260 with
    | false =>
      simp only [d109067, d146313, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d109067, d146313, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  exact h16 p ha hb
theorem andIntro26642 (p : Pattern) (ha : d109073 p = 1) (hb : d142666 p = 1) : d146319 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d142666 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d109068 q = 1) (hb : d142666 q = 1) : d146314 q = 1 := by
    cases bit : q 259 with
    | false =>
      simp only [d109068, d146314, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26641 q ha hb
    | true =>
      simp only [d109068, d146314, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d109069 q = 1) (hb : d142666 q = 1) : d146315 q = 1 := by
    cases bit : q 258 with
    | false =>
      simp only [d109069, d146315, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d109069, d146315, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d109070 q = 1) (hb : d142666 q = 1) : d146316 q = 1 := by
    cases bit : q 257 with
    | false =>
      simp only [d109070, d146316, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d109070, d146316, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d109071 q = 1) (hb : d142666 q = 1) : d146317 q = 1 := by
    cases bit : q 256 with
    | false =>
      simp only [d109071, d146317, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d109071, d146317, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d109072 q = 1) (hb : d142666 q = 1) : d146318 q = 1 := by
    cases bit : q 255 with
    | false =>
      simp only [d109072, d146318, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d109072, d146318, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d109073 q = 1) (hb : d142666 q = 1) : d146319 q = 1 := by
    cases bit : q 254 with
    | false =>
      simp only [d109073, d146319, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d109073, d146319, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro26643 (p : Pattern) (ha : d109079 p = 1) (hb : d142666 p = 1) : d146325 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d142666 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d109074 q = 1) (hb : d142666 q = 1) : d146320 q = 1 := by
    cases bit : q 253 with
    | false =>
      simp only [d109074, d146320, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26642 q ha hb
    | true =>
      simp only [d109074, d146320, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d109075 q = 1) (hb : d142666 q = 1) : d146321 q = 1 := by
    cases bit : q 252 with
    | false =>
      simp only [d109075, d146321, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d109075, d146321, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d109076 q = 1) (hb : d142666 q = 1) : d146322 q = 1 := by
    cases bit : q 251 with
    | false =>
      simp only [d109076, d146322, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d109076, d146322, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d109077 q = 1) (hb : d142666 q = 1) : d146323 q = 1 := by
    cases bit : q 250 with
    | false =>
      simp only [d109077, d146323, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d109077, d146323, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d109078 q = 1) (hb : d142666 q = 1) : d146324 q = 1 := by
    cases bit : q 249 with
    | false =>
      simp only [d109078, d146324, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d109078, d146324, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d109079 q = 1) (hb : d142666 q = 1) : d146325 q = 1 := by
    cases bit : q 245 with
    | false =>
      simp only [d109079, d146325, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d109079, d146325, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro26644 (p : Pattern) (ha : d109085 p = 1) (hb : d142666 p = 1) : d146331 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d142666 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d109080 q = 1) (hb : d142666 q = 1) : d146326 q = 1 := by
    cases bit : q 200 with
    | false =>
      simp only [d109080, d146326, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26643 q ha hb
    | true =>
      simp only [d109080, d146326, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d109081 q = 1) (hb : d142666 q = 1) : d146327 q = 1 := by
    cases bit : q 199 with
    | false =>
      simp only [d109081, d146327, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d109081, d146327, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d109082 q = 1) (hb : d142666 q = 1) : d146328 q = 1 := by
    cases bit : q 186 with
    | false =>
      simp only [d109082, d146328, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d109082, d146328, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d109083 q = 1) (hb : d142666 q = 1) : d146329 q = 1 := by
    cases bit : q 185 with
    | false =>
      simp only [d109083, d146329, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d109083, d146329, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d109084 q = 1) (hb : d142666 q = 1) : d146330 q = 1 := by
    cases bit : q 184 with
    | false =>
      simp only [d109084, d146330, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d109084, d146330, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d109085 q = 1) (hb : d142666 q = 1) : d146331 q = 1 := by
    cases bit : q 181 with
    | false =>
      simp only [d109085, d146331, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d109085, d146331, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro26645 (p : Pattern) (ha : d109091 p = 1) (hb : d142666 p = 1) : d146337 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d142666 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d109086 q = 1) (hb : d142666 q = 1) : d146332 q = 1 := by
    cases bit : q 177 with
    | false =>
      simp only [d109086, d146332, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26644 q ha hb
    | true =>
      simp only [d109086, d146332, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d109087 q = 1) (hb : d142666 q = 1) : d146333 q = 1 := by
    cases bit : q 164 with
    | false =>
      simp only [d109087, d146333, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d109087, d146333, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d109088 q = 1) (hb : d142666 q = 1) : d146334 q = 1 := by
    cases bit : q 156 with
    | false =>
      simp only [d109088, d146334, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d109088, d146334, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d109089 q = 1) (hb : d142666 q = 1) : d146335 q = 1 := by
    cases bit : q 155 with
    | false =>
      simp only [d109089, d146335, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d109089, d146335, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d109090 q = 1) (hb : d142666 q = 1) : d146336 q = 1 := by
    cases bit : q 134 with
    | false =>
      simp only [d109090, d146336, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d109090, d146336, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d109091 q = 1) (hb : d142666 q = 1) : d146337 q = 1 := by
    cases bit : q 133 with
    | false =>
      simp only [d109091, d146337, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d109091, d146337, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro26646 (p : Pattern) (ha : d109097 p = 1) (hb : d142666 p = 1) : d146343 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d142666 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d109092 q = 1) (hb : d142666 q = 1) : d146338 q = 1 := by
    cases bit : q 120 with
    | false =>
      simp only [d109092, d146338, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26645 q ha hb
    | true =>
      simp only [d109092, d146338, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d109093 q = 1) (hb : d142666 q = 1) : d146339 q = 1 := by
    cases bit : q 118 with
    | false =>
      simp only [d109093, d146339, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d109093, d146339, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d109094 q = 1) (hb : d142666 q = 1) : d146340 q = 1 := by
    cases bit : q 114 with
    | false =>
      simp only [d109094, d146340, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d109094, d146340, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d109095 q = 1) (hb : d142666 q = 1) : d146341 q = 1 := by
    cases bit : q 111 with
    | false =>
      simp only [d109095, d146341, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d109095, d146341, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d109096 q = 1) (hb : d142666 q = 1) : d146342 q = 1 := by
    cases bit : q 98 with
    | false =>
      simp only [d109096, d146342, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d109096, d146342, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d109097 q = 1) (hb : d142666 q = 1) : d146343 q = 1 := by
    cases bit : q 97 with
    | false =>
      simp only [d109097, d146343, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d109097, d146343, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro26647 (p : Pattern) (ha : d109103 p = 1) (hb : d142666 p = 1) : d146349 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d142666 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d109098 q = 1) (hb : d142666 q = 1) : d146344 q = 1 := by
    cases bit : q 94 with
    | false =>
      simp only [d109098, d146344, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26646 q ha hb
    | true =>
      simp only [d109098, d146344, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d109099 q = 1) (hb : d142666 q = 1) : d146345 q = 1 := by
    cases bit : q 76 with
    | false =>
      simp only [d109099, d146345, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d109099, d146345, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d109100 q = 1) (hb : d142666 q = 1) : d146346 q = 1 := by
    cases bit : q 67 with
    | false =>
      simp only [d109100, d146346, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d109100, d146346, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d109101 q = 1) (hb : d142666 q = 1) : d146347 q = 1 := by
    cases bit : q 52 with
    | false =>
      simp only [d109101, d146347, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d109101, d146347, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d109102 q = 1) (hb : d142666 q = 1) : d146348 q = 1 := by
    cases bit : q 47 with
    | false =>
      simp only [d109102, d146348, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d109102, d146348, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d109103 q = 1) (hb : d142666 q = 1) : d146349 q = 1 := by
    cases bit : q 46 with
    | false =>
      simp only [d109103, d146349, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d109103, d146349, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro26648 (p : Pattern) (ha : d109109 p = 1) (hb : d142666 p = 1) : d146355 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d142666 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d109104 q = 1) (hb : d142666 q = 1) : d146350 q = 1 := by
    cases bit : q 45 with
    | false =>
      simp only [d109104, d146350, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26647 q ha hb
    | true =>
      simp only [d109104, d146350, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d109105 q = 1) (hb : d142666 q = 1) : d146351 q = 1 := by
    cases bit : q 30 with
    | false =>
      simp only [d109105, d146351, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d109105, d146351, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d109106 q = 1) (hb : d142666 q = 1) : d146352 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d109106, d146352, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d109106, d146352, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d109107 q = 1) (hb : d142666 q = 1) : d146353 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d109107, d146353, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d109107, d146353, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d109108 q = 1) (hb : d142666 q = 1) : d146354 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d109108, d146354, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d109108, d146354, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d109109 q = 1) (hb : d142666 q = 1) : d146355 q = 1 := by
    cases bit : q 25 with
    | false =>
      simp only [d109109, d146355, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d109109, d146355, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro26649 (p : Pattern) (ha : d51880 p = 1) (hb : d120066 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d51880 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d25 q = 1) (hb : d51877 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d25, d51877, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro2 q ha hb
    | true =>
      simp only [d25, d51877, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d26 q = 1) (hb : d51878 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d26, d51878, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d26, d51878, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h4 (q : Pattern) (ha : d27 q = 1) (hb : d51879 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d27, d51879, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d27, d51879, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d28 q = 1) (hb : d51880 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d28, d51880, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d28, d51880, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h6 (q : Pattern) (ha : d29 q = 1) (hb : d51880 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d29, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d29, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d51880 q = 1) (hb : d120066 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d120066, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d120066, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  exact h7 p ha hb
theorem andIntro26650 (p : Pattern) (ha : d120072 p = 1) (hb : d144109 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d120067 q = 1) (hb : d144104 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d120067, d144104, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26649 q hb ha
    | true =>
      simp only [d120067, d144104, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d120068 q = 1) (hb : d144105 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d120068, d144105, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d120068, d144105, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d120069 q = 1) (hb : d144106 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d120069, d144106, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d120069, d144106, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d120070 q = 1) (hb : d144107 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d120070, d144107, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d120070, d144107, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d120071 q = 1) (hb : d144108 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d120071, d144108, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d120071, d144108, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d120072 q = 1) (hb : d144109 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d120072, d144109, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d120072, d144109, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro26651 (p : Pattern) (ha : d120078 p = 1) (hb : d144115 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d120073 q = 1) (hb : d144110 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d120073, d144110, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26650 q ha hb
    | true =>
      simp only [d120073, d144110, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d120074 q = 1) (hb : d144111 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d120074, d144111, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d120074, d144111, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d120075 q = 1) (hb : d144112 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d120075, d144112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d120075, d144112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d120076 q = 1) (hb : d144113 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d120076, d144113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d120076, d144113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d120077 q = 1) (hb : d144114 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d120077, d144114, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d120077, d144114, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d120078 q = 1) (hb : d144115 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d120078, d144115, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d120078, d144115, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro26652 (p : Pattern) (ha : d120084 p = 1) (hb : d144121 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d120079 q = 1) (hb : d144116 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d120079, d144116, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26651 q ha hb
    | true =>
      simp only [d120079, d144116, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d120080 q = 1) (hb : d144117 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d120080, d144117, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d120080, d144117, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d120081 q = 1) (hb : d144118 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d120081, d144118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d120081, d144118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d120082 q = 1) (hb : d144119 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d120082, d144119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d120082, d144119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d120083 q = 1) (hb : d144120 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d120083, d144120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d120083, d144120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d120084 q = 1) (hb : d144121 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d120084, d144121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d120084, d144121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro26653 (p : Pattern) (ha : d120085 p = 1) (hb : d144122 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d120073 q = 1) (hb : d144110 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d120073, d144110, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26650 q ha hb
    | true =>
      simp only [d120073, d144110, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d120074 q = 1) (hb : d144111 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d120074, d144111, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d120074, d144111, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d120075 q = 1) (hb : d144112 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d120075, d144112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d120075, d144112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d120076 q = 1) (hb : d144113 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d120076, d144113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d120076, d144113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d120077 q = 1) (hb : d144114 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d120077, d144114, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d120077, d144114, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d120085 q = 1) (hb : d144122 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d120085, d144122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d120085, d144122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro26654 (p : Pattern) (ha : d120091 p = 1) (hb : d144128 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d120079 q = 1) (hb : d144116 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d120079, d144116, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26651 q ha hb
    | true =>
      simp only [d120079, d144116, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d120080 q = 1) (hb : d144117 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d120080, d144117, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d120080, d144117, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d120081 q = 1) (hb : d144118 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d120081, d144118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d120081, d144118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d120082 q = 1) (hb : d144119 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d120082, d144119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d120082, d144119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d120083 q = 1) (hb : d144120 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d120083, d144120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d120083, d144120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d120086 q = 1) (hb : d144123 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d120086, d144123, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26653 q ha hb
    | true =>
      simp only [d120086, d144123, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d120087 q = 1) (hb : d144124 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d120087, d144124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d120087, d144124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d120088 q = 1) (hb : d144125 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d120088, d144125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d120088, d144125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d120089 q = 1) (hb : d144126 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d120089, d144126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d120089, d144126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d120090 q = 1) (hb : d144127 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d120090, d144127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d120090, d144127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d120091 q = 1) (hb : d144128 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d120091, d144128, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d120091, d144128, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro26655 (p : Pattern) (ha : d120096 p = 1) (hb : d144133 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d120086 q = 1) (hb : d144123 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d120086, d144123, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26653 q ha hb
    | true =>
      simp only [d120086, d144123, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d120087 q = 1) (hb : d144124 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d120087, d144124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d120087, d144124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d120088 q = 1) (hb : d144125 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d120088, d144125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d120088, d144125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d120089 q = 1) (hb : d144126 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d120089, d144126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d120089, d144126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d120090 q = 1) (hb : d144127 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d120090, d144127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d120090, d144127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d120096 q = 1) (hb : d144133 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d120096, d144133, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d120096, d144133, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro26656 (p : Pattern) (ha : d51921 p = 1) (hb : d120102 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d51921 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d66 q = 1) (hb : d51918 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d66, d51918, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d66, d51918, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro2 q ha hb
  have h3 (q : Pattern) (ha : d25 q = 1) (hb : d51877 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d25, d51877, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro2 q ha hb
    | true =>
      simp only [d25, d51877, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h4 (q : Pattern) (ha : d67 q = 1) (hb : d51919 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d67, d51919, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d67, d51919, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d26 q = 1) (hb : d51878 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d26, d51878, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d26, d51878, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h6 (q : Pattern) (ha : d68 q = 1) (hb : d51920 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d68, d51920, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d68, d51920, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d69 q = 1) (hb : d51921 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d69, d51921, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d69, d51921, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h8 (q : Pattern) (ha : d70 q = 1) (hb : d51921 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d70, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d70, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d51921 q = 1) (hb : d120102 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d120102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d120102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  exact h9 p ha hb
theorem andIntro26657 (p : Pattern) (ha : d120108 p = 1) (hb : d144144 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d120103 q = 1) (hb : d144139 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d120103, d144139, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26656 q hb ha
    | true =>
      simp only [d120103, d144139, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d120104 q = 1) (hb : d144140 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d120104, d144140, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d120104, d144140, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d120105 q = 1) (hb : d144141 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d120105, d144141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d120105, d144141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d120106 q = 1) (hb : d144142 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d120106, d144142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d120106, d144142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d120107 q = 1) (hb : d144143 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d120107, d144143, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d120107, d144143, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d120108 q = 1) (hb : d144144 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d120108, d144144, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d120108, d144144, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro26658 (p : Pattern) (ha : d120114 p = 1) (hb : d144150 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d120109 q = 1) (hb : d144145 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d120109, d144145, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26657 q ha hb
    | true =>
      simp only [d120109, d144145, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d120110 q = 1) (hb : d144146 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d120110, d144146, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d120110, d144146, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d120111 q = 1) (hb : d144147 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d120111, d144147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d120111, d144147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d120112 q = 1) (hb : d144148 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d120112, d144148, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d120112, d144148, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d120113 q = 1) (hb : d144149 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d120113, d144149, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d120113, d144149, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d120114 q = 1) (hb : d144150 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d120114, d144150, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d120114, d144150, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro26659 (p : Pattern) (ha : d120120 p = 1) (hb : d144156 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d120115 q = 1) (hb : d144151 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d120115, d144151, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26658 q ha hb
    | true =>
      simp only [d120115, d144151, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d120116 q = 1) (hb : d144152 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d120116, d144152, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d120116, d144152, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d120117 q = 1) (hb : d144153 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d120117, d144153, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d120117, d144153, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d120118 q = 1) (hb : d144154 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d120118, d144154, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d120118, d144154, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d120119 q = 1) (hb : d144155 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d120119, d144155, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d120119, d144155, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d120120 q = 1) (hb : d144156 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d120120, d144156, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d120120, d144156, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro26660 (p : Pattern) (ha : d120126 p = 1) (hb : d144162 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d120092 q = 1) (hb : d144129 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d120092, d144129, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26652 q ha hb
    | true =>
      simp only [d120092, d144129, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26654 q ha hb
  have h2 (q : Pattern) (ha : d120093 q = 1) (hb : d144130 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d120093, d144130, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d120093, d144130, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d120094 q = 1) (hb : d144131 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d120094, d144131, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d120094, d144131, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d120095 q = 1) (hb : d144132 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d120095, d144132, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d120095, d144132, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d120097 q = 1) (hb : d144134 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d120097, d144134, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d120097, d144134, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26655 q ha hb
  have h6 (q : Pattern) (ha : d120098 q = 1) (hb : d144135 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d120098, d144135, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d120098, d144135, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d120099 q = 1) (hb : d144136 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d120099, d144136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d120099, d144136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d120100 q = 1) (hb : d144137 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d120100, d144137, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d120100, d144137, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d120101 q = 1) (hb : d144138 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d120101, d144138, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d120101, d144138, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d120121 q = 1) (hb : d144157 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d120121, d144157, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d120121, d144157, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26659 q ha hb
  have h11 (q : Pattern) (ha : d120122 q = 1) (hb : d144158 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d120122, d144158, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d120122, d144158, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d120123 q = 1) (hb : d144159 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d120123, d144159, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d120123, d144159, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d120124 q = 1) (hb : d144160 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d120124, d144160, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d120124, d144160, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d120125 q = 1) (hb : d144161 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d120125, d144161, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d120125, d144161, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d120126 q = 1) (hb : d144162 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d120126, d144162, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d120126, d144162, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro26661 (p : Pattern) (ha : d120136 p = 1) (hb : d144172 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d120079 q = 1) (hb : d144116 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d120079, d144116, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26651 q ha hb
    | true =>
      simp only [d120079, d144116, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d120132 q = 1) (hb : d144168 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d120132, d144168, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d120132, d144168, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d120133 q = 1) (hb : d144169 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d120133, d144169, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d120133, d144169, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d120134 q = 1) (hb : d144170 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d120134, d144170, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d120134, d144170, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d120135 q = 1) (hb : d144171 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d120135, d144171, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d120135, d144171, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d120136 q = 1) (hb : d144172 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d120136, d144172, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d120136, d144172, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro26662 (p : Pattern) (ha : d120143 p = 1) (hb : d144179 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d120079 q = 1) (hb : d144116 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d120079, d144116, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26651 q ha hb
    | true =>
      simp only [d120079, d144116, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d120132 q = 1) (hb : d144168 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d120132, d144168, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d120132, d144168, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d120133 q = 1) (hb : d144169 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d120133, d144169, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d120133, d144169, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d120134 q = 1) (hb : d144170 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d120134, d144170, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d120134, d144170, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d120135 q = 1) (hb : d144171 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d120135, d144171, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d120135, d144171, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d120086 q = 1) (hb : d144123 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d120086, d144123, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26653 q ha hb
    | true =>
      simp only [d120086, d144123, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d120139 q = 1) (hb : d144175 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d120139, d144175, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d120139, d144175, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d120140 q = 1) (hb : d144176 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d120140, d144176, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d120140, d144176, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d120141 q = 1) (hb : d144177 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d120141, d144177, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d120141, d144177, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d120142 q = 1) (hb : d144178 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d120142, d144178, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d120142, d144178, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d120143 q = 1) (hb : d144179 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d120143, d144179, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d120143, d144179, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro26663 (p : Pattern) (ha : d120195 p = 1) (hb : d144230 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d120079 q = 1) (hb : d144116 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d120079, d144116, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26651 q ha hb
    | true =>
      simp only [d120079, d144116, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d120132 q = 1) (hb : d144168 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d120132, d144168, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d120132, d144168, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d120133 q = 1) (hb : d144169 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d120133, d144169, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d120133, d144169, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d120134 q = 1) (hb : d144170 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d120134, d144170, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d120134, d144170, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d120135 q = 1) (hb : d144171 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d120135, d144171, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d120135, d144171, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d120195 q = 1) (hb : d144230 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d120195, d144230, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d120195, d144230, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro26664 (p : Pattern) (ha : d120148 p = 1) (hb : d144184 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d120073 q = 1) (hb : d144110 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d120073, d144110, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26650 q ha hb
    | true =>
      simp only [d120073, d144110, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d120074 q = 1) (hb : d144111 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d120074, d144111, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d120074, d144111, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d120075 q = 1) (hb : d144112 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d120075, d144112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d120075, d144112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d120076 q = 1) (hb : d144113 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d120076, d144113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d120076, d144113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d120147 q = 1) (hb : d144183 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d120147, d144183, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d120147, d144183, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d120148 q = 1) (hb : d144184 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d120148, d144184, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d120148, d144184, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro26665 (p : Pattern) (ha : d120155 p = 1) (hb : d144191 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d120073 q = 1) (hb : d144110 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d120073, d144110, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26650 q ha hb
    | true =>
      simp only [d120073, d144110, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d120074 q = 1) (hb : d144111 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d120074, d144111, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d120074, d144111, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d120075 q = 1) (hb : d144112 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d120075, d144112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d120075, d144112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d120153 q = 1) (hb : d144189 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d120153, d144189, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d120153, d144189, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d120154 q = 1) (hb : d144190 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d120154, d144190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d120154, d144190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d120155 q = 1) (hb : d144191 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d120155, d144191, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d120155, d144191, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro26666 (p : Pattern) (ha : d51993 p = 1) (hb : d145277 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d51993 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d139 q = 1) (hb : d51990 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d139, d51990, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19 q ha hb
    | true =>
      simp only [d139, d51990, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d140 q = 1) (hb : d51991 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d140, d51991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d140, d51991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h4 (q : Pattern) (ha : d141 q = 1) (hb : d51992 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d141, d51992, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d141, d51992, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d142 q = 1) (hb : d51993 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d142, d51993, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d142, d51993, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h6 (q : Pattern) (ha : d13980 q = 1) (hb : d51993 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d13980, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d13980, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d51993 q = 1) (hb : d145277 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d145277, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d145277, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  exact h7 p ha hb
theorem andIntro26667 (p : Pattern) (ha : d144200 p = 1) (hb : d145283 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d51880 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d144195 q = 1) (hb : d145278 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d144195, d145278, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26666 q ha hb
    | true =>
      simp only [d144195, d145278, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d144196 q = 1) (hb : d145279 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d144196, d145279, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d144196, d145279, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d144197 q = 1) (hb : d145280 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d144197, d145280, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d144197, d145280, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d120067 q = 1) (hb : d144104 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d120067, d144104, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26649 q hb ha
    | true =>
      simp only [d120067, d144104, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d120068 q = 1) (hb : d144105 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d120068, d144105, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d120068, d144105, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d120069 q = 1) (hb : d144106 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d120069, d144106, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d120069, d144106, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d144198 q = 1) (hb : d145281 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d144198, d145281, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d144198, d145281, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
  have h9 (q : Pattern) (ha : d120070 q = 1) (hb : d144107 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d120070, d144107, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d120070, d144107, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d144199 q = 1) (hb : d145282 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d144199, d145282, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d144199, d145282, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
  have h11 (q : Pattern) (ha : d144200 q = 1) (hb : d145283 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d144200, d145283, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d144200, d145283, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h11 p ha hb
theorem andIntro26668 (p : Pattern) (ha : d144206 p = 1) (hb : d145289 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d144201 q = 1) (hb : d145284 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d144201, d145284, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26667 q ha hb
    | true =>
      simp only [d144201, d145284, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d144202 q = 1) (hb : d145285 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d144202, d145285, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d144202, d145285, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d120073 q = 1) (hb : d144110 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d120073, d144110, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26650 q ha hb
    | true =>
      simp only [d120073, d144110, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d120074 q = 1) (hb : d144111 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d120074, d144111, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d120074, d144111, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d144203 q = 1) (hb : d145286 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d144203, d145286, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d144203, d145286, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d144204 q = 1) (hb : d145287 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d144204, d145287, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d144204, d145287, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d144205 q = 1) (hb : d145288 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d144205, d145288, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d144205, d145288, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d144206 q = 1) (hb : d145289 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d144206, d145289, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d144206, d145289, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro26669 (p : Pattern) (ha : d144212 p = 1) (hb : d145295 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d120149 q = 1) (hb : d144185 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d120149, d144185, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26664 q ha hb
    | true =>
      simp only [d120149, d144185, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d120150 q = 1) (hb : d144186 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d120150, d144186, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d120150, d144186, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d120151 q = 1) (hb : d144187 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d120151, d144187, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d120151, d144187, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d120152 q = 1) (hb : d144188 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d120152, d144188, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d120152, d144188, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d120156 q = 1) (hb : d144192 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d120156, d144192, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26665 q ha hb
    | true =>
      simp only [d120156, d144192, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d120157 q = 1) (hb : d144193 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d120157, d144193, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d120157, d144193, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d120158 q = 1) (hb : d144194 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d120158, d144194, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d120158, d144194, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d144207 q = 1) (hb : d145290 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d144207, d145290, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26668 q ha hb
    | true =>
      simp only [d144207, d145290, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26651 q hb ha
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d144116 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d144208 q = 1) (hb : d145291 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d144208, d145291, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d144208, d145291, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
  have h11 (q : Pattern) (ha : d120079 q = 1) (hb : d144116 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d120079, d144116, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26651 q ha hb
    | true =>
      simp only [d120079, d144116, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d120080 q = 1) (hb : d144117 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d120080, d144117, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d120080, d144117, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d144209 q = 1) (hb : d145292 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d144209, d145292, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d144209, d145292, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
  have h14 (q : Pattern) (ha : d144210 q = 1) (hb : d145293 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d144210, d145293, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
    | true =>
      simp only [d144210, d145293, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d144211 q = 1) (hb : d145294 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d144211, d145294, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d144211, d145294, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d144212 q = 1) (hb : d145295 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d144212, d145295, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d144212, d145295, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  exact h16 p ha hb
theorem andIntro26670 (p : Pattern) (ha : d120178 p = 1) (hb : d144213 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d120073 q = 1) (hb : d144110 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d120073, d144110, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26650 q ha hb
    | true =>
      simp only [d120073, d144110, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d120074 q = 1) (hb : d144111 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d120074, d144111, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d120074, d144111, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d120075 q = 1) (hb : d144112 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d120075, d144112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d120075, d144112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d120076 q = 1) (hb : d144113 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d120076, d144113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d120076, d144113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d120147 q = 1) (hb : d144183 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d120147, d144183, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d120147, d144183, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d120178 q = 1) (hb : d144213 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d120178, d144213, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d120178, d144213, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro26671 (p : Pattern) (ha : d120183 p = 1) (hb : d144218 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d120073 q = 1) (hb : d144110 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d120073, d144110, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26650 q ha hb
    | true =>
      simp only [d120073, d144110, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d120074 q = 1) (hb : d144111 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d120074, d144111, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d120074, d144111, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d120075 q = 1) (hb : d144112 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d120075, d144112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d120075, d144112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d120153 q = 1) (hb : d144189 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d120153, d144189, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d120153, d144189, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d120154 q = 1) (hb : d144190 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d120154, d144190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d120154, d144190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d120183 q = 1) (hb : d144218 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d120183, d144218, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d120183, d144218, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro26672 (p : Pattern) (ha : d144222 p = 1) (hb : d145296 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d144201 q = 1) (hb : d145284 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d144201, d145284, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26667 q ha hb
    | true =>
      simp only [d144201, d145284, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d144202 q = 1) (hb : d145285 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d144202, d145285, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d144202, d145285, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d120073 q = 1) (hb : d144110 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d120073, d144110, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26650 q ha hb
    | true =>
      simp only [d120073, d144110, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d120074 q = 1) (hb : d144111 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d120074, d144111, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d120074, d144111, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d144203 q = 1) (hb : d145286 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d144203, d145286, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d144203, d145286, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d144204 q = 1) (hb : d145287 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d144204, d145287, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d144204, d145287, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d144205 q = 1) (hb : d145288 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d144205, d145288, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d144205, d145288, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d144222 q = 1) (hb : d145296 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d144222, d145296, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d144222, d145296, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro26673 (p : Pattern) (ha : d144228 p = 1) (hb : d145302 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d120149 q = 1) (hb : d144185 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d120149, d144185, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26664 q ha hb
    | true =>
      simp only [d120149, d144185, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d120150 q = 1) (hb : d144186 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d120150, d144186, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d120150, d144186, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d120151 q = 1) (hb : d144187 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d120151, d144187, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d120151, d144187, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d120152 q = 1) (hb : d144188 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d120152, d144188, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d120152, d144188, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d120156 q = 1) (hb : d144192 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d120156, d144192, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26665 q ha hb
    | true =>
      simp only [d120156, d144192, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d120157 q = 1) (hb : d144193 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d120157, d144193, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d120157, d144193, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d120158 q = 1) (hb : d144194 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d120158, d144194, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d120158, d144194, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d144207 q = 1) (hb : d145290 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d144207, d145290, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26668 q ha hb
    | true =>
      simp only [d144207, d145290, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26651 q hb ha
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d144116 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d144208 q = 1) (hb : d145291 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d144208, d145291, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d144208, d145291, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
  have h11 (q : Pattern) (ha : d120079 q = 1) (hb : d144116 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d120079, d144116, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26651 q ha hb
    | true =>
      simp only [d120079, d144116, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d120080 q = 1) (hb : d144117 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d120080, d144117, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d120080, d144117, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d144209 q = 1) (hb : d145292 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d144209, d145292, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d144209, d145292, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
  have h14 (q : Pattern) (ha : d144210 q = 1) (hb : d145293 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d144210, d145293, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
    | true =>
      simp only [d144210, d145293, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d144211 q = 1) (hb : d145294 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d144211, d145294, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d144211, d145294, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d120179 q = 1) (hb : d144214 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d120179, d144214, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26670 q ha hb
    | true =>
      simp only [d120179, d144214, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h17 (q : Pattern) (ha : d120180 q = 1) (hb : d144215 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d120180, d144215, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d120180, d144215, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d120181 q = 1) (hb : d144216 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d120181, d144216, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d120181, d144216, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h19 (q : Pattern) (ha : d120182 q = 1) (hb : d144217 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d120182, d144217, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d120182, d144217, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d120184 q = 1) (hb : d144219 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d120184, d144219, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26671 q ha hb
    | true =>
      simp only [d120184, d144219, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h21 (q : Pattern) (ha : d120185 q = 1) (hb : d144220 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d120185, d144220, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d120185, d144220, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
  have h22 (q : Pattern) (ha : d120186 q = 1) (hb : d144221 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d120186, d144221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d120186, d144221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h23 (q : Pattern) (ha : d144223 q = 1) (hb : d145297 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d144223, d145297, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26672 q ha hb
    | true =>
      simp only [d144223, d145297, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26653 q hb ha
  have h24 (q : Pattern) (ha : d0 q = 1) (hb : d144123 q = 1) : d0 q = 1 := by
    exact ha
  have h25 (q : Pattern) (ha : d144224 q = 1) (hb : d145298 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d144224, d145298, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
    | true =>
      simp only [d144224, d145298, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q hb ha
  have h26 (q : Pattern) (ha : d120086 q = 1) (hb : d144123 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d120086, d144123, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26653 q ha hb
    | true =>
      simp only [d120086, d144123, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h27 (q : Pattern) (ha : d120087 q = 1) (hb : d144124 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d120087, d144124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h26 q ha hb
    | true =>
      simp only [d120087, d144124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h28 (q : Pattern) (ha : d144225 q = 1) (hb : d145299 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d144225, d145299, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q ha hb
    | true =>
      simp only [d144225, d145299, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h27 q hb ha
  have h29 (q : Pattern) (ha : d144226 q = 1) (hb : d145300 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d144226, d145300, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q hb ha
    | true =>
      simp only [d144226, d145300, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h28 q ha hb
  have h30 (q : Pattern) (ha : d144227 q = 1) (hb : d145301 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d144227, d145301, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q hb ha
    | true =>
      simp only [d144227, d145301, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h29 q ha hb
  have h31 (q : Pattern) (ha : d144228 q = 1) (hb : d145302 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d144228, d145302, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d144228, d145302, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h30 q ha hb
  exact h31 p ha hb
theorem andIntro26674 (p : Pattern) (ha : d144237 p = 1) (hb : d145309 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d144223 q = 1) (hb : d145297 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d144223, d145297, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26672 q ha hb
    | true =>
      simp only [d144223, d145297, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26653 q hb ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d144123 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d144224 q = 1) (hb : d145298 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d144224, d145298, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d144224, d145298, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d120086 q = 1) (hb : d144123 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d120086, d144123, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26653 q ha hb
    | true =>
      simp only [d120086, d144123, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d120087 q = 1) (hb : d144124 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d120087, d144124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d120087, d144124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d144225 q = 1) (hb : d145299 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d144225, d145299, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d144225, d145299, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d144235 q = 1) (hb : d145307 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d144235, d145307, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d144235, d145307, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d144236 q = 1) (hb : d145308 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d144236, d145308, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d144236, d145308, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d144237 q = 1) (hb : d145309 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d144237, d145309, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d144237, d145309, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro26675 (p : Pattern) (ha : d52047 p = 1) (hb : d145315 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d52047 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d226 q = 1) (hb : d52044 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d226, d52044, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d226, d52044, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19 q ha hb
  have h3 (q : Pattern) (ha : d139 q = 1) (hb : d51990 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d139, d51990, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19 q ha hb
    | true =>
      simp only [d139, d51990, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h4 (q : Pattern) (ha : d227 q = 1) (hb : d52045 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d227, d52045, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d227, d52045, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d140 q = 1) (hb : d51991 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d140, d51991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d140, d51991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h6 (q : Pattern) (ha : d228 q = 1) (hb : d52046 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d228, d52046, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d228, d52046, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d229 q = 1) (hb : d52047 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d229, d52047, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d229, d52047, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h8 (q : Pattern) (ha : d14019 q = 1) (hb : d52047 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d14019, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d14019, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d52047 q = 1) (hb : d145315 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d145315, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d145315, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  exact h9 p ha hb
theorem andIntro26676 (p : Pattern) (ha : d144248 p = 1) (hb : d145321 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d51921 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d144243 q = 1) (hb : d145316 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d144243, d145316, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26675 q ha hb
    | true =>
      simp only [d144243, d145316, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d144244 q = 1) (hb : d145317 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d144244, d145317, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d144244, d145317, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d144245 q = 1) (hb : d145318 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d144245, d145318, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d144245, d145318, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d120103 q = 1) (hb : d144139 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d120103, d144139, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26656 q hb ha
    | true =>
      simp only [d120103, d144139, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d120104 q = 1) (hb : d144140 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d120104, d144140, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d120104, d144140, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d120105 q = 1) (hb : d144141 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d120105, d144141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d120105, d144141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d144246 q = 1) (hb : d145319 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d144246, d145319, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d144246, d145319, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
  have h9 (q : Pattern) (ha : d120106 q = 1) (hb : d144142 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d120106, d144142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d120106, d144142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d144247 q = 1) (hb : d145320 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d144247, d145320, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d144247, d145320, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
  have h11 (q : Pattern) (ha : d144248 q = 1) (hb : d145321 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d144248, d145321, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d144248, d145321, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h11 p ha hb
theorem andIntro26677 (p : Pattern) (ha : d144254 p = 1) (hb : d145327 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d144249 q = 1) (hb : d145322 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d144249, d145322, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26676 q ha hb
    | true =>
      simp only [d144249, d145322, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d144250 q = 1) (hb : d145323 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d144250, d145323, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d144250, d145323, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d120109 q = 1) (hb : d144145 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d120109, d144145, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26657 q ha hb
    | true =>
      simp only [d120109, d144145, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d120110 q = 1) (hb : d144146 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d120110, d144146, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d120110, d144146, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d144251 q = 1) (hb : d145324 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d144251, d145324, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d144251, d145324, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d144252 q = 1) (hb : d145325 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d144252, d145325, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d144252, d145325, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d144253 q = 1) (hb : d145326 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d144253, d145326, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d144253, d145326, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d144254 q = 1) (hb : d145327 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d144254, d145327, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d144254, d145327, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro26678 (p : Pattern) (ha : d144260 p = 1) (hb : d145333 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d144255 q = 1) (hb : d145328 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d144255, d145328, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26677 q ha hb
    | true =>
      simp only [d144255, d145328, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26658 q hb ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d144151 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d144256 q = 1) (hb : d145329 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d144256, d145329, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d144256, d145329, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d120115 q = 1) (hb : d144151 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d120115, d144151, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26658 q ha hb
    | true =>
      simp only [d120115, d144151, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d120116 q = 1) (hb : d144152 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d120116, d144152, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d120116, d144152, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d144257 q = 1) (hb : d145330 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d144257, d145330, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d144257, d145330, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d144258 q = 1) (hb : d145331 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d144258, d145331, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d144258, d145331, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d144259 q = 1) (hb : d145332 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d144259, d145332, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d144259, d145332, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d144260 q = 1) (hb : d145333 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d144260, d145333, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d144260, d145333, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro26679 (p : Pattern) (ha : d144266 p = 1) (hb : d145339 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d120137 q = 1) (hb : d144173 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d120137, d144173, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d120137, d144173, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26661 q ha hb
  have h2 (q : Pattern) (ha : d120138 q = 1) (hb : d144174 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d120138, d144174, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d120138, d144174, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d120144 q = 1) (hb : d144180 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d120144, d144180, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26661 q ha hb
    | true =>
      simp only [d120144, d144180, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26662 q ha hb
  have h4 (q : Pattern) (ha : d120145 q = 1) (hb : d144181 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d120145, d144181, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d120145, d144181, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d120146 q = 1) (hb : d144182 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d120146, d144182, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d120146, d144182, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d144229 q = 1) (hb : d145303 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d144229, d145303, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26669 q ha hb
    | true =>
      simp only [d144229, d145303, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26673 q ha hb
  have h7 (q : Pattern) (ha : d120196 q = 1) (hb : d144231 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d120196, d144231, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26663 q ha hb
    | true =>
      simp only [d120196, d144231, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d144232 q = 1) (hb : d145304 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d144232, d145304, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d144232, d145304, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
  have h9 (q : Pattern) (ha : d144233 q = 1) (hb : d145305 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d144233, d145305, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d144233, d145305, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h10 (q : Pattern) (ha : d144234 q = 1) (hb : d145306 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d144234, d145306, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
    | true =>
      simp only [d144234, d145306, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d144238 q = 1) (hb : d145310 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d144238, d145310, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d144238, d145310, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26674 q ha hb
  have h12 (q : Pattern) (ha : d144239 q = 1) (hb : d145311 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d144239, d145311, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d144239, d145311, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d144240 q = 1) (hb : d145312 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d144240, d145312, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d144240, d145312, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h14 (q : Pattern) (ha : d144241 q = 1) (hb : d145313 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d144241, d145313, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d144241, d145313, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h15 (q : Pattern) (ha : d144242 q = 1) (hb : d145314 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d144242, d145314, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d144242, d145314, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d144261 q = 1) (hb : d145334 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d144261, d145334, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d144261, d145334, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26678 q ha hb
  have h17 (q : Pattern) (ha : d144262 q = 1) (hb : d145335 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d144262, d145335, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d144262, d145335, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h18 (q : Pattern) (ha : d144263 q = 1) (hb : d145336 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d144263, d145336, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d144263, d145336, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h19 (q : Pattern) (ha : d144264 q = 1) (hb : d145337 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d144264, d145337, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d144264, d145337, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h20 (q : Pattern) (ha : d144265 q = 1) (hb : d145338 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d144265, d145338, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d144265, d145338, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h21 (q : Pattern) (ha : d144266 q = 1) (hb : d145339 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d144266, d145339, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d144266, d145339, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
  exact h21 p ha hb
theorem andIntro26680 (p : Pattern) (ha : d144272 p = 1) (hb : d145345 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d120127 q = 1) (hb : d144163 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d120127, d144163, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d120127, d144163, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26660 q ha hb
  have h2 (q : Pattern) (ha : d120128 q = 1) (hb : d144164 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d120128, d144164, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d120128, d144164, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d120129 q = 1) (hb : d144165 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d120129, d144165, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d120129, d144165, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d120130 q = 1) (hb : d144166 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d120130, d144166, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d120130, d144166, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d120131 q = 1) (hb : d144167 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d120131, d144167, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d120131, d144167, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d144267 q = 1) (hb : d145340 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d144267, d145340, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d144267, d145340, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26679 q ha hb
  have h7 (q : Pattern) (ha : d144268 q = 1) (hb : d145341 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d144268, d145341, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d144268, d145341, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d144269 q = 1) (hb : d145342 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d144269, d145342, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d144269, d145342, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d144270 q = 1) (hb : d145343 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d144270, d145343, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d144270, d145343, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d144271 q = 1) (hb : d145344 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d144271, d145344, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d144271, d145344, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d144272 q = 1) (hb : d145345 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d144272, d145345, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
    | true =>
      simp only [d144272, d145345, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro26681 (p : Pattern) (ha : d120334 p = 1) (hb : d144353 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d120086 q = 1) (hb : d144123 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d120086, d144123, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26653 q ha hb
    | true =>
      simp only [d120086, d144123, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d120139 q = 1) (hb : d144175 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d120139, d144175, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d120139, d144175, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d120140 q = 1) (hb : d144176 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d120140, d144176, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d120140, d144176, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d120141 q = 1) (hb : d144177 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d120141, d144177, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d120141, d144177, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d120142 q = 1) (hb : d144178 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d120142, d144178, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d120142, d144178, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d120334 q = 1) (hb : d144353 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d120334, d144353, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d120334, d144353, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro26682 (p : Pattern) (ha : d120378 p = 1) (hb : d144388 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d120115 q = 1) (hb : d144151 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d120115, d144151, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26658 q ha hb
    | true =>
      simp only [d120115, d144151, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d120374 q = 1) (hb : d144384 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d120374, d144384, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d120374, d144384, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d120375 q = 1) (hb : d144385 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d120375, d144385, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d120375, d144385, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d120376 q = 1) (hb : d144386 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d120376, d144386, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d120376, d144386, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d120377 q = 1) (hb : d144387 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d120377, d144387, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d120377, d144387, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d120378 q = 1) (hb : d144388 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d120378, d144388, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d120378, d144388, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro26683 (p : Pattern) (ha : d144277 p = 1) (hb : d145350 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d144207 q = 1) (hb : d145290 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d144207, d145290, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26668 q ha hb
    | true =>
      simp only [d144207, d145290, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26651 q hb ha
  have h2 (q : Pattern) (ha : d144273 q = 1) (hb : d145346 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d144273, d145346, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d144273, d145346, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d144274 q = 1) (hb : d145347 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d144274, d145347, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d144274, d145347, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d144275 q = 1) (hb : d145348 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d144275, d145348, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d144275, d145348, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d144276 q = 1) (hb : d145349 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d144276, d145349, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d144276, d145349, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d144277 q = 1) (hb : d145350 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d144277, d145350, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d144277, d145350, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro26684 (p : Pattern) (ha : d144284 p = 1) (hb : d145357 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d144207 q = 1) (hb : d145290 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d144207, d145290, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26668 q ha hb
    | true =>
      simp only [d144207, d145290, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26651 q hb ha
  have h2 (q : Pattern) (ha : d144273 q = 1) (hb : d145346 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d144273, d145346, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d144273, d145346, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d144274 q = 1) (hb : d145347 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d144274, d145347, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d144274, d145347, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d144275 q = 1) (hb : d145348 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d144275, d145348, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d144275, d145348, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d144276 q = 1) (hb : d145349 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d144276, d145349, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d144276, d145349, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d144223 q = 1) (hb : d145297 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d144223, d145297, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26672 q ha hb
    | true =>
      simp only [d144223, d145297, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26653 q hb ha
  have h7 (q : Pattern) (ha : d144280 q = 1) (hb : d145353 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d144280, d145353, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d144280, d145353, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d144281 q = 1) (hb : d145354 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d144281, d145354, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d144281, d145354, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d144282 q = 1) (hb : d145355 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d144282, d145355, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d144282, d145355, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d144283 q = 1) (hb : d145356 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d144283, d145356, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d144283, d145356, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d144284 q = 1) (hb : d145357 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d144284, d145357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d144284, d145357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro26685 (p : Pattern) (ha : d144289 p = 1) (hb : d145362 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d144201 q = 1) (hb : d145284 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d144201, d145284, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26667 q ha hb
    | true =>
      simp only [d144201, d145284, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d144202 q = 1) (hb : d145285 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d144202, d145285, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d144202, d145285, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d120073 q = 1) (hb : d144110 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d120073, d144110, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26650 q ha hb
    | true =>
      simp only [d120073, d144110, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d120074 q = 1) (hb : d144111 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d120074, d144111, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d120074, d144111, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d144203 q = 1) (hb : d145286 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d144203, d145286, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d144203, d145286, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d144204 q = 1) (hb : d145287 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d144204, d145287, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d144204, d145287, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d144288 q = 1) (hb : d145361 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d144288, d145361, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d144288, d145361, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d144289 q = 1) (hb : d145362 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d144289, d145362, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d144289, d145362, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro26686 (p : Pattern) (ha : d144296 p = 1) (hb : d145369 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d144201 q = 1) (hb : d145284 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d144201, d145284, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26667 q ha hb
    | true =>
      simp only [d144201, d145284, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d144202 q = 1) (hb : d145285 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d144202, d145285, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d144202, d145285, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d120073 q = 1) (hb : d144110 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d120073, d144110, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26650 q ha hb
    | true =>
      simp only [d120073, d144110, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d120074 q = 1) (hb : d144111 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d120074, d144111, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d120074, d144111, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d144203 q = 1) (hb : d145286 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d144203, d145286, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d144203, d145286, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d144294 q = 1) (hb : d145367 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d144294, d145367, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d144294, d145367, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d144295 q = 1) (hb : d145368 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d144295, d145368, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d144295, d145368, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d144296 q = 1) (hb : d145369 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d144296, d145369, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d144296, d145369, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro26687 (p : Pattern) (ha : d52121 p = 1) (hb : d145373 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d52121 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d319 q = 1) (hb : d52118 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d319, d52118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42 q ha hb
    | true =>
      simp only [d319, d52118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d320 q = 1) (hb : d52119 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d320, d52119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d320, d52119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h4 (q : Pattern) (ha : d321 q = 1) (hb : d52120 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d321, d52120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d321, d52120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d322 q = 1) (hb : d52121 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d322, d52121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d322, d52121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h6 (q : Pattern) (ha : d14077 q = 1) (hb : d52121 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d14077, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d14077, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d52121 q = 1) (hb : d145373 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d145373, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d145373, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  exact h7 p ha hb
theorem andIntro26688 (p : Pattern) (ha : d144305 p = 1) (hb : d145379 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d51993 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d144300 q = 1) (hb : d145374 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d144300, d145374, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26687 q ha hb
    | true =>
      simp only [d144300, d145374, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d144301 q = 1) (hb : d145375 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d144301, d145375, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d144301, d145375, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d144302 q = 1) (hb : d145376 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d144302, d145376, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d144302, d145376, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d51880 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d144195 q = 1) (hb : d145278 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d144195, d145278, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26666 q ha hb
    | true =>
      simp only [d144195, d145278, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d144196 q = 1) (hb : d145279 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d144196, d145279, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d144196, d145279, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d144197 q = 1) (hb : d145280 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d144197, d145280, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d144197, d145280, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d144303 q = 1) (hb : d145377 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d144303, d145377, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d144303, d145377, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d120067 q = 1) (hb : d144104 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d120067, d144104, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26649 q hb ha
    | true =>
      simp only [d120067, d144104, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d120068 q = 1) (hb : d144105 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d120068, d144105, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d120068, d144105, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d120069 q = 1) (hb : d144106 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d120069, d144106, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d120069, d144106, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d144198 q = 1) (hb : d145281 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d144198, d145281, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d144198, d145281, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
  have h14 (q : Pattern) (ha : d144304 q = 1) (hb : d145378 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d144304, d145378, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d144304, d145378, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d144305 q = 1) (hb : d145379 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d144305, d145379, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d144305, d145379, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h15 p ha hb
theorem andIntro26689 (p : Pattern) (ha : d144311 p = 1) (hb : d145385 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d144306 q = 1) (hb : d145380 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d144306, d145380, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26688 q ha hb
    | true =>
      simp only [d144306, d145380, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d144307 q = 1) (hb : d145381 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d144307, d145381, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d144307, d145381, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d144201 q = 1) (hb : d145284 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d144201, d145284, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26667 q ha hb
    | true =>
      simp only [d144201, d145284, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d144202 q = 1) (hb : d145285 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d144202, d145285, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d144202, d145285, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d144308 q = 1) (hb : d145382 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d144308, d145382, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d144308, d145382, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d144309 q = 1) (hb : d145383 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d144309, d145383, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d144309, d145383, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d144310 q = 1) (hb : d145384 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d144310, d145384, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d144310, d145384, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d144311 q = 1) (hb : d145385 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d144311, d145385, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d144311, d145385, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro26690 (p : Pattern) (ha : d144317 p = 1) (hb : d145391 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d144201 q = 1) (hb : d145284 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d144201, d145284, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26667 q ha hb
    | true =>
      simp only [d144201, d145284, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d144202 q = 1) (hb : d145285 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d144202, d145285, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d144202, d145285, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d144314 q = 1) (hb : d145388 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d144314, d145388, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d144314, d145388, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d144315 q = 1) (hb : d145389 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d144315, d145389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d144315, d145389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d144316 q = 1) (hb : d145390 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d144316, d145390, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d144316, d145390, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d144317 q = 1) (hb : d145391 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d144317, d145391, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d144317, d145391, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro26691 (p : Pattern) (ha : d144323 p = 1) (hb : d145397 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d144290 q = 1) (hb : d145363 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d144290, d145363, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26685 q ha hb
    | true =>
      simp only [d144290, d145363, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26664 q hb ha
  have h2 (q : Pattern) (ha : d144291 q = 1) (hb : d145364 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d144291, d145364, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d144291, d145364, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d144292 q = 1) (hb : d145365 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d144292, d145365, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d144292, d145365, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d144293 q = 1) (hb : d145366 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d144293, d145366, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d144293, d145366, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d144297 q = 1) (hb : d145370 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d144297, d145370, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26686 q ha hb
    | true =>
      simp only [d144297, d145370, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26665 q hb ha
  have h6 (q : Pattern) (ha : d144298 q = 1) (hb : d145371 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d144298, d145371, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d144298, d145371, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d144299 q = 1) (hb : d145372 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d144299, d145372, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d144299, d145372, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d144312 q = 1) (hb : d145386 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d144312, d145386, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26689 q ha hb
    | true =>
      simp only [d144312, d145386, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26668 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d144207 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d144313 q = 1) (hb : d145387 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d144313, d145387, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d144313, d145387, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
  have h11 (q : Pattern) (ha : d144318 q = 1) (hb : d145392 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d144318, d145392, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26690 q ha hb
    | true =>
      simp only [d144318, d145392, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d144319 q = 1) (hb : d145393 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d144319, d145393, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d144319, d145393, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d144320 q = 1) (hb : d145394 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d144320, d145394, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d144320, d145394, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d144321 q = 1) (hb : d145395 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d144321, d145395, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d144321, d145395, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d144322 q = 1) (hb : d145396 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d144322, d145396, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d144322, d145396, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d144323 q = 1) (hb : d145397 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d144323, d145397, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d144323, d145397, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  exact h16 p ha hb
theorem andIntro26692 (p : Pattern) (ha : d144324 p = 1) (hb : d145398 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d144201 q = 1) (hb : d145284 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d144201, d145284, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26667 q ha hb
    | true =>
      simp only [d144201, d145284, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d144202 q = 1) (hb : d145285 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d144202, d145285, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d144202, d145285, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d120073 q = 1) (hb : d144110 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d120073, d144110, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26650 q ha hb
    | true =>
      simp only [d120073, d144110, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d120074 q = 1) (hb : d144111 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d120074, d144111, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d120074, d144111, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d144203 q = 1) (hb : d145286 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d144203, d145286, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d144203, d145286, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d144204 q = 1) (hb : d145287 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d144204, d145287, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d144204, d145287, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d144288 q = 1) (hb : d145361 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d144288, d145361, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d144288, d145361, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d144324 q = 1) (hb : d145398 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d144324, d145398, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d144324, d145398, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro26693 (p : Pattern) (ha : d144329 p = 1) (hb : d145403 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d144201 q = 1) (hb : d145284 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d144201, d145284, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26667 q ha hb
    | true =>
      simp only [d144201, d145284, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d144202 q = 1) (hb : d145285 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d144202, d145285, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d144202, d145285, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d120073 q = 1) (hb : d144110 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d120073, d144110, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26650 q ha hb
    | true =>
      simp only [d120073, d144110, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d120074 q = 1) (hb : d144111 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d120074, d144111, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d120074, d144111, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d144203 q = 1) (hb : d145286 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d144203, d145286, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d144203, d145286, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d144294 q = 1) (hb : d145367 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d144294, d145367, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d144294, d145367, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d144295 q = 1) (hb : d145368 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d144295, d145368, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d144295, d145368, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d144329 q = 1) (hb : d145403 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d144329, d145403, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d144329, d145403, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro26694 (p : Pattern) (ha : d144333 p = 1) (hb : d145407 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d144306 q = 1) (hb : d145380 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d144306, d145380, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26688 q ha hb
    | true =>
      simp only [d144306, d145380, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d144307 q = 1) (hb : d145381 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d144307, d145381, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d144307, d145381, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d144201 q = 1) (hb : d145284 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d144201, d145284, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26667 q ha hb
    | true =>
      simp only [d144201, d145284, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d144202 q = 1) (hb : d145285 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d144202, d145285, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d144202, d145285, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d144308 q = 1) (hb : d145382 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d144308, d145382, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d144308, d145382, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d144309 q = 1) (hb : d145383 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d144309, d145383, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d144309, d145383, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d144310 q = 1) (hb : d145384 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d144310, d145384, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d144310, d145384, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d144333 q = 1) (hb : d145407 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d144333, d145407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d144333, d145407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro26695 (p : Pattern) (ha : d144336 p = 1) (hb : d145410 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d144201 q = 1) (hb : d145284 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d144201, d145284, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26667 q ha hb
    | true =>
      simp only [d144201, d145284, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d144202 q = 1) (hb : d145285 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d144202, d145285, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d144202, d145285, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d144314 q = 1) (hb : d145388 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d144314, d145388, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d144314, d145388, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d144315 q = 1) (hb : d145389 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d144315, d145389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d144315, d145389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d144316 q = 1) (hb : d145390 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d144316, d145390, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d144316, d145390, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d144336 q = 1) (hb : d145410 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d144336, d145410, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d144336, d145410, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro26696 (p : Pattern) (ha : d144342 p = 1) (hb : d145416 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d144290 q = 1) (hb : d145363 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d144290, d145363, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26685 q ha hb
    | true =>
      simp only [d144290, d145363, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26664 q hb ha
  have h2 (q : Pattern) (ha : d144291 q = 1) (hb : d145364 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d144291, d145364, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d144291, d145364, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d144292 q = 1) (hb : d145365 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d144292, d145365, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d144292, d145365, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d144293 q = 1) (hb : d145366 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d144293, d145366, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d144293, d145366, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d144297 q = 1) (hb : d145370 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d144297, d145370, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26686 q ha hb
    | true =>
      simp only [d144297, d145370, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26665 q hb ha
  have h6 (q : Pattern) (ha : d144298 q = 1) (hb : d145371 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d144298, d145371, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d144298, d145371, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d144299 q = 1) (hb : d145372 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d144299, d145372, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d144299, d145372, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d144312 q = 1) (hb : d145386 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d144312, d145386, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26689 q ha hb
    | true =>
      simp only [d144312, d145386, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26668 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d144207 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d144313 q = 1) (hb : d145387 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d144313, d145387, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d144313, d145387, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
  have h11 (q : Pattern) (ha : d144318 q = 1) (hb : d145392 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d144318, d145392, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26690 q ha hb
    | true =>
      simp only [d144318, d145392, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d144319 q = 1) (hb : d145393 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d144319, d145393, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d144319, d145393, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d144320 q = 1) (hb : d145394 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d144320, d145394, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d144320, d145394, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d144321 q = 1) (hb : d145395 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d144321, d145395, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d144321, d145395, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d144322 q = 1) (hb : d145396 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d144322, d145396, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d144322, d145396, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d144325 q = 1) (hb : d145399 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d144325, d145399, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26692 q ha hb
    | true =>
      simp only [d144325, d145399, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26670 q hb ha
  have h17 (q : Pattern) (ha : d144326 q = 1) (hb : d145400 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d144326, d145400, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d144326, d145400, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d144327 q = 1) (hb : d145401 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d144327, d145401, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d144327, d145401, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h19 (q : Pattern) (ha : d144328 q = 1) (hb : d145402 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d144328, d145402, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d144328, d145402, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d144330 q = 1) (hb : d145404 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d144330, d145404, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26693 q ha hb
    | true =>
      simp only [d144330, d145404, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26671 q hb ha
  have h21 (q : Pattern) (ha : d144331 q = 1) (hb : d145405 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d144331, d145405, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d144331, d145405, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
  have h22 (q : Pattern) (ha : d144332 q = 1) (hb : d145406 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d144332, d145406, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d144332, d145406, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h23 (q : Pattern) (ha : d144334 q = 1) (hb : d145408 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d144334, d145408, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26694 q ha hb
    | true =>
      simp only [d144334, d145408, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26672 q ha hb
  have h24 (q : Pattern) (ha : d0 q = 1) (hb : d144223 q = 1) : d0 q = 1 := by
    exact ha
  have h25 (q : Pattern) (ha : d144335 q = 1) (hb : d145409 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d144335, d145409, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
    | true =>
      simp only [d144335, d145409, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q hb ha
  have h26 (q : Pattern) (ha : d144337 q = 1) (hb : d145411 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d144337, d145411, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26695 q ha hb
    | true =>
      simp only [d144337, d145411, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h27 (q : Pattern) (ha : d144338 q = 1) (hb : d145412 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d144338, d145412, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h26 q ha hb
    | true =>
      simp only [d144338, d145412, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h28 (q : Pattern) (ha : d144339 q = 1) (hb : d145413 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d144339, d145413, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q ha hb
    | true =>
      simp only [d144339, d145413, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h27 q ha hb
  have h29 (q : Pattern) (ha : d144340 q = 1) (hb : d145414 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d144340, d145414, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
    | true =>
      simp only [d144340, d145414, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h28 q ha hb
  have h30 (q : Pattern) (ha : d144341 q = 1) (hb : d145415 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d144341, d145415, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d144341, d145415, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h29 q ha hb
  have h31 (q : Pattern) (ha : d144342 q = 1) (hb : d145416 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d144342, d145416, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d144342, d145416, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h30 q ha hb
  exact h31 p ha hb
theorem andIntro26697 (p : Pattern) (ha : d144344 p = 1) (hb : d145418 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d144207 q = 1) (hb : d145290 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d144207, d145290, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26668 q ha hb
    | true =>
      simp only [d144207, d145290, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26651 q hb ha
  have h2 (q : Pattern) (ha : d144273 q = 1) (hb : d145346 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d144273, d145346, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d144273, d145346, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d144274 q = 1) (hb : d145347 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d144274, d145347, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d144274, d145347, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d144275 q = 1) (hb : d145348 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d144275, d145348, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d144275, d145348, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d144276 q = 1) (hb : d145349 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d144276, d145349, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d144276, d145349, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d120079 q = 1) (hb : d144116 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d120079, d144116, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26651 q ha hb
    | true =>
      simp only [d120079, d144116, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d120132 q = 1) (hb : d144168 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d120132, d144168, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d120132, d144168, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d120133 q = 1) (hb : d144169 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d120133, d144169, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d120133, d144169, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d120134 q = 1) (hb : d144170 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d120134, d144170, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d120134, d144170, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d120135 q = 1) (hb : d144171 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d120135, d144171, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d120135, d144171, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d144344 q = 1) (hb : d145418 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d144344, d145418, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d144344, d145418, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
  exact h11 p ha hb
theorem andIntro26698 (p : Pattern) (ha : d144351 p = 1) (hb : d145425 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d144334 q = 1) (hb : d145408 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d144334, d145408, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26694 q ha hb
    | true =>
      simp only [d144334, d145408, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26672 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d144223 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d144335 q = 1) (hb : d145409 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d144335, d145409, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d144335, d145409, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d144337 q = 1) (hb : d145411 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d144337, d145411, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26695 q ha hb
    | true =>
      simp only [d144337, d145411, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d144338 q = 1) (hb : d145412 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d144338, d145412, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d144338, d145412, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d144339 q = 1) (hb : d145413 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d144339, d145413, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d144339, d145413, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d144349 q = 1) (hb : d145423 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d144349, d145423, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d144349, d145423, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d144350 q = 1) (hb : d145424 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d144350, d145424, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d144350, d145424, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d144351 q = 1) (hb : d145425 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d144351, d145425, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d144351, d145425, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro26699 (p : Pattern) (ha : d52181 p = 1) (hb : d145431 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d52181 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d412 q = 1) (hb : d52178 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d412, d52178, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d412, d52178, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42 q ha hb
  have h3 (q : Pattern) (ha : d319 q = 1) (hb : d52118 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d319, d52118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42 q ha hb
    | true =>
      simp only [d319, d52118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h4 (q : Pattern) (ha : d413 q = 1) (hb : d52179 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d413, d52179, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d413, d52179, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d320 q = 1) (hb : d52119 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d320, d52119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d320, d52119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h6 (q : Pattern) (ha : d414 q = 1) (hb : d52180 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d414, d52180, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d414, d52180, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d415 q = 1) (hb : d52181 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d415, d52181, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d415, d52181, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h8 (q : Pattern) (ha : d14154 q = 1) (hb : d52181 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d14154, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d14154, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d52181 q = 1) (hb : d145431 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d145431, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d145431, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  exact h9 p ha hb
theorem andIntro26700 (p : Pattern) (ha : d144364 p = 1) (hb : d145437 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d52047 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d144359 q = 1) (hb : d145432 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d144359, d145432, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26699 q ha hb
    | true =>
      simp only [d144359, d145432, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d144360 q = 1) (hb : d145433 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d144360, d145433, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d144360, d145433, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d144361 q = 1) (hb : d145434 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d144361, d145434, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d144361, d145434, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d51921 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d144243 q = 1) (hb : d145316 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d144243, d145316, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26675 q ha hb
    | true =>
      simp only [d144243, d145316, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d144244 q = 1) (hb : d145317 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d144244, d145317, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d144244, d145317, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d144245 q = 1) (hb : d145318 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d144245, d145318, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d144245, d145318, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d144362 q = 1) (hb : d145435 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d144362, d145435, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d144362, d145435, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d120103 q = 1) (hb : d144139 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d120103, d144139, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26656 q hb ha
    | true =>
      simp only [d120103, d144139, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d120104 q = 1) (hb : d144140 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d120104, d144140, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d120104, d144140, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d120105 q = 1) (hb : d144141 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d120105, d144141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d120105, d144141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d144246 q = 1) (hb : d145319 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d144246, d145319, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d144246, d145319, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
  have h14 (q : Pattern) (ha : d144363 q = 1) (hb : d145436 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d144363, d145436, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d144363, d145436, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d144364 q = 1) (hb : d145437 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d144364, d145437, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d144364, d145437, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h15 p ha hb
theorem andIntro26701 (p : Pattern) (ha : d144370 p = 1) (hb : d145443 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d144365 q = 1) (hb : d145438 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d144365, d145438, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26700 q ha hb
    | true =>
      simp only [d144365, d145438, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d144366 q = 1) (hb : d145439 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d144366, d145439, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d144366, d145439, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d144249 q = 1) (hb : d145322 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d144249, d145322, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26676 q ha hb
    | true =>
      simp only [d144249, d145322, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d144250 q = 1) (hb : d145323 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d144250, d145323, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d144250, d145323, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d144367 q = 1) (hb : d145440 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d144367, d145440, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d144367, d145440, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d144368 q = 1) (hb : d145441 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d144368, d145441, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d144368, d145441, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d144369 q = 1) (hb : d145442 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d144369, d145442, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d144369, d145442, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d144370 q = 1) (hb : d145443 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d144370, d145443, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d144370, d145443, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro26702 (p : Pattern) (ha : d144376 p = 1) (hb : d145449 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d144249 q = 1) (hb : d145322 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d144249, d145322, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26676 q ha hb
    | true =>
      simp only [d144249, d145322, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d144250 q = 1) (hb : d145323 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d144250, d145323, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d144250, d145323, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d144373 q = 1) (hb : d145446 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d144373, d145446, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d144373, d145446, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d144374 q = 1) (hb : d145447 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d144374, d145447, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d144374, d145447, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d144375 q = 1) (hb : d145448 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d144375, d145448, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d144375, d145448, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d144376 q = 1) (hb : d145449 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d144376, d145449, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d144376, d145449, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro26703 (p : Pattern) (ha : d144382 p = 1) (hb : d145455 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d144371 q = 1) (hb : d145444 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d144371, d145444, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26701 q ha hb
    | true =>
      simp only [d144371, d145444, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26677 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d144255 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d144372 q = 1) (hb : d145445 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d144372, d145445, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d144372, d145445, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d144377 q = 1) (hb : d145450 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d144377, d145450, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26702 q ha hb
    | true =>
      simp only [d144377, d145450, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d144378 q = 1) (hb : d145451 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d144378, d145451, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d144378, d145451, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d144379 q = 1) (hb : d145452 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d144379, d145452, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d144379, d145452, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d144380 q = 1) (hb : d145453 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d144380, d145453, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d144380, d145453, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d144381 q = 1) (hb : d145454 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d144381, d145454, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d144381, d145454, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d144382 q = 1) (hb : d145455 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d144382, d145455, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d144382, d145455, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro26704 (p : Pattern) (ha : d144394 p = 1) (hb : d145461 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d144278 q = 1) (hb : d145351 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d144278, d145351, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d144278, d145351, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26683 q ha hb
  have h2 (q : Pattern) (ha : d144279 q = 1) (hb : d145352 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d144279, d145352, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d144279, d145352, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d144285 q = 1) (hb : d145358 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d144285, d145358, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26683 q ha hb
    | true =>
      simp only [d144285, d145358, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26684 q ha hb
  have h4 (q : Pattern) (ha : d144286 q = 1) (hb : d145359 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d144286, d145359, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d144286, d145359, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d144287 q = 1) (hb : d145360 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d144287, d145360, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d144287, d145360, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d144343 q = 1) (hb : d145417 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d144343, d145417, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26691 q ha hb
    | true =>
      simp only [d144343, d145417, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26696 q ha hb
  have h7 (q : Pattern) (ha : d144345 q = 1) (hb : d145419 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d144345, d145419, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26697 q ha hb
    | true =>
      simp only [d144345, d145419, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26662 q hb ha
  have h8 (q : Pattern) (ha : d144346 q = 1) (hb : d145420 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d144346, d145420, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d144346, d145420, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d144347 q = 1) (hb : d145421 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d144347, d145421, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d144347, d145421, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h10 (q : Pattern) (ha : d144348 q = 1) (hb : d145422 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d144348, d145422, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d144348, d145422, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d144352 q = 1) (hb : d145426 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d144352, d145426, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d144352, d145426, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26698 q ha hb
  have h12 (q : Pattern) (ha : d120335 q = 1) (hb : d144354 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d120335, d144354, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d120335, d144354, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26681 q ha hb
  have h13 (q : Pattern) (ha : d144355 q = 1) (hb : d145427 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d144355, d145427, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d144355, d145427, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
  have h14 (q : Pattern) (ha : d144356 q = 1) (hb : d145428 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d144356, d145428, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d144356, d145428, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h15 (q : Pattern) (ha : d144357 q = 1) (hb : d145429 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d144357, d145429, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d144357, d145429, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h16 (q : Pattern) (ha : d144358 q = 1) (hb : d145430 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d144358, d145430, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d144358, d145430, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d144383 q = 1) (hb : d145456 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d144383, d145456, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d144383, d145456, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26703 q ha hb
  have h18 (q : Pattern) (ha : d120379 q = 1) (hb : d144389 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d120379, d144389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d120379, d144389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26682 q ha hb
  have h19 (q : Pattern) (ha : d144390 q = 1) (hb : d145457 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d144390, d145457, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d144390, d145457, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q hb ha
  have h20 (q : Pattern) (ha : d144391 q = 1) (hb : d145458 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d144391, d145458, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d144391, d145458, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h21 (q : Pattern) (ha : d144392 q = 1) (hb : d145459 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d144392, d145459, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d144392, d145459, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h22 (q : Pattern) (ha : d144393 q = 1) (hb : d145460 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d144393, d145460, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d144393, d145460, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h23 (q : Pattern) (ha : d144394 q = 1) (hb : d145461 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d144394, d145461, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d144394, d145461, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
  exact h23 p ha hb
theorem andIntro26705 (p : Pattern) (ha : d144400 p = 1) (hb : d145467 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d144395 q = 1) (hb : d145462 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d144395, d145462, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d144395, d145462, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26704 q ha hb
  have h2 (q : Pattern) (ha : d144396 q = 1) (hb : d145463 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d144396, d145463, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d144396, d145463, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d144397 q = 1) (hb : d145464 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d144397, d145464, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d144397, d145464, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d144398 q = 1) (hb : d145465 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d144398, d145465, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d144398, d145465, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d144399 q = 1) (hb : d145466 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d144399, d145466, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d144399, d145466, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d144400 q = 1) (hb : d145467 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d144400, d145467, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d144400, d145467, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro26706 (p : Pattern) (ha : d52431 p = 1) (hb : d120392 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d52431 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d751 q = 1) (hb : d52428 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d751, d52428, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100 q ha hb
    | true =>
      simp only [d751, d52428, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d752 q = 1) (hb : d52429 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d752, d52429, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d752, d52429, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h4 (q : Pattern) (ha : d753 q = 1) (hb : d52430 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d753, d52430, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d753, d52430, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d754 q = 1) (hb : d52431 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d754, d52431, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d754, d52431, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h6 (q : Pattern) (ha : d757 q = 1) (hb : d52431 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d757, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d757, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d52431 q = 1) (hb : d120392 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d120392, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d120392, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  exact h7 p ha hb
theorem andIntro26707 (p : Pattern) (ha : d120406 p = 1) (hb : d144415 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d120397 q = 1) (hb : d144405 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d120397, d144405, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26706 q hb ha
    | true =>
      simp only [d120397, d144405, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d120398 q = 1) (hb : d144406 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d120398, d144406, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d120398, d144406, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d120399 q = 1) (hb : d144407 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d120399, d144407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d120399, d144407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d120400 q = 1) (hb : d144409 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d120400, d144409, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d120400, d144409, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d120405 q = 1) (hb : d144414 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d120405, d144414, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d120405, d144414, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d120406 q = 1) (hb : d144415 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d120406, d144415, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d120406, d144415, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro26708 (p : Pattern) (ha : d120416 p = 1) (hb : d144425 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d120407 q = 1) (hb : d144416 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d120407, d144416, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26707 q ha hb
    | true =>
      simp only [d120407, d144416, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d120408 q = 1) (hb : d144417 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d120408, d144417, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d120408, d144417, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d120413 q = 1) (hb : d144422 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d120413, d144422, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d120413, d144422, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d120414 q = 1) (hb : d144423 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d120414, d144423, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d120414, d144423, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d120415 q = 1) (hb : d144424 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d120415, d144424, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d120415, d144424, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d120416 q = 1) (hb : d144425 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d120416, d144425, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d120416, d144425, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro26709 (p : Pattern) (ha : d120426 p = 1) (hb : d144435 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d120407 q = 1) (hb : d144416 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d120407, d144416, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26707 q ha hb
    | true =>
      simp only [d120407, d144416, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d120408 q = 1) (hb : d144417 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d120408, d144417, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d120408, d144417, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d120413 q = 1) (hb : d144422 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d120413, d144422, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d120413, d144422, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d120414 q = 1) (hb : d144423 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d120414, d144423, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d120414, d144423, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d120415 q = 1) (hb : d144424 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d120415, d144424, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d120415, d144424, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d120426 q = 1) (hb : d144435 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d120426, d144435, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d120426, d144435, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro26710 (p : Pattern) (ha : d120525 p = 1) (hb : d144519 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d120514 q = 1) (hb : d144508 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d120514, d144508, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26708 q ha hb
    | true =>
      simp only [d120514, d144508, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d120515 q = 1) (hb : d144509 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d120515, d144509, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d120515, d144509, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d120516 q = 1) (hb : d144510 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d120516, d144510, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d120516, d144510, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d120517 q = 1) (hb : d144511 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d120517, d144511, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d120517, d144511, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d120518 q = 1) (hb : d144512 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d120518, d144512, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d120518, d144512, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d120520 q = 1) (hb : d144514 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d120520, d144514, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26709 q ha hb
    | true =>
      simp only [d120520, d144514, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d120521 q = 1) (hb : d144515 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d120521, d144515, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d120521, d144515, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d120522 q = 1) (hb : d144516 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d120522, d144516, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d120522, d144516, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d120523 q = 1) (hb : d144517 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d120523, d144517, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d120523, d144517, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d120524 q = 1) (hb : d144518 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d120524, d144518, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d120524, d144518, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d120525 q = 1) (hb : d144519 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d120525, d144519, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d120525, d144519, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro26711 (p : Pattern) (ha : d120534 p = 1) (hb : d144528 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d120520 q = 1) (hb : d144514 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d120520, d144514, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26709 q ha hb
    | true =>
      simp only [d120520, d144514, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d120521 q = 1) (hb : d144515 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d120521, d144515, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d120521, d144515, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d120522 q = 1) (hb : d144516 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d120522, d144516, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d120522, d144516, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d120523 q = 1) (hb : d144517 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d120523, d144517, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d120523, d144517, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d120524 q = 1) (hb : d144518 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d120524, d144518, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d120524, d144518, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d120534 q = 1) (hb : d144528 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d120534, d144528, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d120534, d144528, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro26712 (p : Pattern) (ha : d52593 p = 1) (hb : d120545 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d52593 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d971 q = 1) (hb : d52590 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d971, d52590, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d971, d52590, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100 q ha hb
  have h3 (q : Pattern) (ha : d751 q = 1) (hb : d52428 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d751, d52428, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100 q ha hb
    | true =>
      simp only [d751, d52428, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h4 (q : Pattern) (ha : d972 q = 1) (hb : d52591 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d972, d52591, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d972, d52591, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d752 q = 1) (hb : d52429 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d752, d52429, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d752, d52429, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h6 (q : Pattern) (ha : d973 q = 1) (hb : d52592 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d973, d52592, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d973, d52592, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d974 q = 1) (hb : d52593 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d974, d52593, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d974, d52593, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h8 (q : Pattern) (ha : d980 q = 1) (hb : d52593 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d980, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d980, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d52593 q = 1) (hb : d120545 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d120545, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d120545, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  exact h9 p ha hb
theorem andIntro26713 (p : Pattern) (ha : d120567 p = 1) (hb : d144559 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d120562 q = 1) (hb : d144541 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d120562, d144541, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26712 q hb ha
    | true =>
      simp only [d120562, d144541, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d120563 q = 1) (hb : d144542 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d120563, d144542, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d120563, d144542, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d120564 q = 1) (hb : d144543 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d120564, d144543, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d120564, d144543, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d120565 q = 1) (hb : d144549 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d120565, d144549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d120565, d144549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d120566 q = 1) (hb : d144558 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d120566, d144558, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d120566, d144558, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d120567 q = 1) (hb : d144559 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d120567, d144559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d120567, d144559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro26714 (p : Pattern) (ha : d120594 p = 1) (hb : d144570 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d120568 q = 1) (hb : d144560 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d120568, d144560, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26713 q ha hb
    | true =>
      simp only [d120568, d144560, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d120569 q = 1) (hb : d144561 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d120569, d144561, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d120569, d144561, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d120591 q = 1) (hb : d144567 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d120591, d144567, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d120591, d144567, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d120592 q = 1) (hb : d144568 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d120592, d144568, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d120592, d144568, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d120593 q = 1) (hb : d144569 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d120593, d144569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d120593, d144569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d120594 q = 1) (hb : d144570 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d120594, d144570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d120594, d144570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro26715 (p : Pattern) (ha : d120600 p = 1) (hb : d144589 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d120595 q = 1) (hb : d144584 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d120595, d144584, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26714 q ha hb
    | true =>
      simp only [d120595, d144584, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d120596 q = 1) (hb : d144585 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d120596, d144585, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d120596, d144585, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d120597 q = 1) (hb : d144586 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d120597, d144586, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d120597, d144586, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d120598 q = 1) (hb : d144587 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d120598, d144587, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d120598, d144587, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d120599 q = 1) (hb : d144588 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d120599, d144588, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d120599, d144588, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d120600 q = 1) (hb : d144589 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d120600, d144589, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d120600, d144589, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro26716 (p : Pattern) (ha : d144411 p = 1) (hb : d145471 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d52431 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d144402 q = 1) (hb : d145374 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d144402, d145374, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26687 q ha hb
    | true =>
      simp only [d144402, d145374, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d144403 q = 1) (hb : d145375 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d144403, d145375, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d144403, d145375, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d144404 q = 1) (hb : d145376 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d144404, d145376, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d144404, d145376, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d120397 q = 1) (hb : d144405 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d120397, d144405, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26706 q hb ha
    | true =>
      simp only [d120397, d144405, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d120398 q = 1) (hb : d144406 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d120398, d144406, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d120398, d144406, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d120399 q = 1) (hb : d144407 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d120399, d144407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d120399, d144407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d144408 q = 1) (hb : d145469 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d144408, d145469, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d144408, d145469, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
  have h9 (q : Pattern) (ha : d120400 q = 1) (hb : d144409 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d120400, d144409, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d120400, d144409, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d144410 q = 1) (hb : d145470 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d144410, d145470, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d144410, d145470, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
  have h11 (q : Pattern) (ha : d144411 q = 1) (hb : d145471 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d144411, d145471, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d144411, d145471, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h11 p ha hb
theorem andIntro26717 (p : Pattern) (ha : d144421 p = 1) (hb : d145477 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d144412 q = 1) (hb : d145472 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d144412, d145472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26716 q ha hb
    | true =>
      simp only [d144412, d145472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d144413 q = 1) (hb : d145473 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d144413, d145473, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d144413, d145473, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d120407 q = 1) (hb : d144416 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d120407, d144416, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26707 q ha hb
    | true =>
      simp only [d120407, d144416, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d120408 q = 1) (hb : d144417 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d120408, d144417, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d120408, d144417, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d144418 q = 1) (hb : d145474 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d144418, d145474, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d144418, d145474, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d144419 q = 1) (hb : d145475 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d144419, d145475, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d144419, d145475, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d144420 q = 1) (hb : d145476 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d144420, d145476, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d144420, d145476, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d144421 q = 1) (hb : d145477 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d144421, d145477, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d144421, d145477, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro26718 (p : Pattern) (ha : d144431 p = 1) (hb : d145483 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d144426 q = 1) (hb : d145478 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d144426, d145478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26717 q ha hb
    | true =>
      simp only [d144426, d145478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26708 q hb ha
  have h2 (q : Pattern) (ha : d144427 q = 1) (hb : d145479 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d144427, d145479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d144427, d145479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d144428 q = 1) (hb : d145480 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d144428, d145480, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d144428, d145480, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d144429 q = 1) (hb : d145481 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d144429, d145481, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d144429, d145481, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d144430 q = 1) (hb : d145482 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d144430, d145482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d144430, d145482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d144431 q = 1) (hb : d145483 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d144431, d145483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d144431, d145483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro26719 (p : Pattern) (ha : d144434 p = 1) (hb : d145486 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d144412 q = 1) (hb : d145472 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d144412, d145472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26716 q ha hb
    | true =>
      simp only [d144412, d145472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d144413 q = 1) (hb : d145473 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d144413, d145473, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d144413, d145473, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d120407 q = 1) (hb : d144416 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d120407, d144416, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26707 q ha hb
    | true =>
      simp only [d120407, d144416, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d120408 q = 1) (hb : d144417 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d120408, d144417, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d120408, d144417, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d144418 q = 1) (hb : d145474 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d144418, d145474, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d144418, d145474, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d144419 q = 1) (hb : d145475 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d144419, d145475, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d144419, d145475, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d144420 q = 1) (hb : d145476 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d144420, d145476, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d144420, d145476, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d144434 q = 1) (hb : d145486 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d144434, d145486, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d144434, d145486, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro26720 (p : Pattern) (ha : d144441 p = 1) (hb : d145492 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d144426 q = 1) (hb : d145478 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d144426, d145478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26717 q ha hb
    | true =>
      simp only [d144426, d145478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26708 q hb ha
  have h2 (q : Pattern) (ha : d144427 q = 1) (hb : d145479 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d144427, d145479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d144427, d145479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d144428 q = 1) (hb : d145480 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d144428, d145480, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d144428, d145480, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d144429 q = 1) (hb : d145481 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d144429, d145481, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d144429, d145481, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d144430 q = 1) (hb : d145482 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d144430, d145482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d144430, d145482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d144436 q = 1) (hb : d145487 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d144436, d145487, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26719 q ha hb
    | true =>
      simp only [d144436, d145487, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26709 q hb ha
  have h7 (q : Pattern) (ha : d144437 q = 1) (hb : d145488 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d144437, d145488, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d144437, d145488, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d144438 q = 1) (hb : d145489 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d144438, d145489, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d144438, d145489, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d144439 q = 1) (hb : d145490 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d144439, d145490, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d144439, d145490, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d144440 q = 1) (hb : d145491 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d144440, d145491, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d144440, d145491, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d144441 q = 1) (hb : d145492 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d144441, d145492, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d144441, d145492, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro26721 (p : Pattern) (ha : d120439 p = 1) (hb : d144448 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d120407 q = 1) (hb : d144416 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d120407, d144416, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26707 q ha hb
    | true =>
      simp only [d120407, d144416, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d120408 q = 1) (hb : d144417 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d120408, d144417, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d120408, d144417, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d120413 q = 1) (hb : d144422 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d120413, d144422, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d120413, d144422, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d120414 q = 1) (hb : d144423 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d120414, d144423, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d120414, d144423, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d120438 q = 1) (hb : d144447 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d120438, d144447, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d120438, d144447, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d120439 q = 1) (hb : d144448 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d120439, d144448, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d120439, d144448, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro26722 (p : Pattern) (ha : d120449 p = 1) (hb : d144458 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d120407 q = 1) (hb : d144416 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d120407, d144416, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26707 q ha hb
    | true =>
      simp only [d120407, d144416, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d120408 q = 1) (hb : d144417 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d120408, d144417, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d120408, d144417, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d120413 q = 1) (hb : d144422 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d120413, d144422, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d120413, d144422, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d120447 q = 1) (hb : d144456 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d120447, d144456, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d120447, d144456, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d120448 q = 1) (hb : d144457 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d120448, d144457, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d120448, d144457, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d120449 q = 1) (hb : d144458 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d120449, d144458, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d120449, d144458, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro26723 (p : Pattern) (ha : d144446 p = 1) (hb : d145497 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d144412 q = 1) (hb : d145472 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d144412, d145472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26716 q ha hb
    | true =>
      simp only [d144412, d145472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d144413 q = 1) (hb : d145473 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d144413, d145473, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d144413, d145473, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d120407 q = 1) (hb : d144416 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d120407, d144416, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26707 q ha hb
    | true =>
      simp only [d120407, d144416, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d120408 q = 1) (hb : d144417 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d120408, d144417, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d120408, d144417, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d144418 q = 1) (hb : d145474 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d144418, d145474, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d144418, d145474, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d144419 q = 1) (hb : d145475 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d144419, d145475, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d144419, d145475, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d144445 q = 1) (hb : d145496 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d144445, d145496, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d144445, d145496, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d144446 q = 1) (hb : d145497 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d144446, d145497, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d144446, d145497, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro26724 (p : Pattern) (ha : d144455 p = 1) (hb : d145504 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d144412 q = 1) (hb : d145472 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d144412, d145472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26716 q ha hb
    | true =>
      simp only [d144412, d145472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d144413 q = 1) (hb : d145473 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d144413, d145473, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d144413, d145473, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d120407 q = 1) (hb : d144416 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d120407, d144416, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26707 q ha hb
    | true =>
      simp only [d120407, d144416, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d120408 q = 1) (hb : d144417 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d120408, d144417, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d120408, d144417, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d144418 q = 1) (hb : d145474 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d144418, d145474, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d144418, d145474, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d144453 q = 1) (hb : d145502 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d144453, d145502, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d144453, d145502, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d144454 q = 1) (hb : d145503 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d144454, d145503, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d144454, d145503, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d144455 q = 1) (hb : d145504 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d144455, d145504, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d144455, d145504, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro26725 (p : Pattern) (ha : d52293 p = 1) (hb : d145508 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d52293 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d543 q = 1) (hb : d52290 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d543, d52290, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro76 q ha hb
    | true =>
      simp only [d543, d52290, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d544 q = 1) (hb : d52291 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d544, d52291, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d544, d52291, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h4 (q : Pattern) (ha : d545 q = 1) (hb : d52292 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d545, d52292, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d545, d52292, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d546 q = 1) (hb : d52293 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d546, d52293, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d546, d52293, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h6 (q : Pattern) (ha : d14261 q = 1) (hb : d52293 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d14261, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d14261, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d52293 q = 1) (hb : d145508 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d145508, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d145508, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  exact h7 p ha hb
theorem andIntro26726 (p : Pattern) (ha : d144467 p = 1) (hb : d145514 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d52121 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d144462 q = 1) (hb : d145509 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d144462, d145509, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26725 q ha hb
    | true =>
      simp only [d144462, d145509, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d144463 q = 1) (hb : d145510 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d144463, d145510, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d144463, d145510, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d144464 q = 1) (hb : d145511 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d144464, d145511, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d144464, d145511, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d52431 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d144402 q = 1) (hb : d145374 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d144402, d145374, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26687 q ha hb
    | true =>
      simp only [d144402, d145374, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d144403 q = 1) (hb : d145375 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d144403, d145375, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d144403, d145375, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d144404 q = 1) (hb : d145376 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d144404, d145376, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d144404, d145376, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d144465 q = 1) (hb : d145512 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d144465, d145512, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d144465, d145512, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d120397 q = 1) (hb : d144405 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d120397, d144405, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26706 q hb ha
    | true =>
      simp only [d120397, d144405, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d120398 q = 1) (hb : d144406 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d120398, d144406, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d120398, d144406, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d120399 q = 1) (hb : d144407 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d120399, d144407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d120399, d144407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d144408 q = 1) (hb : d145469 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d144408, d145469, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d144408, d145469, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
  have h14 (q : Pattern) (ha : d144466 q = 1) (hb : d145513 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d144466, d145513, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d144466, d145513, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d144467 q = 1) (hb : d145514 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d144467, d145514, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d144467, d145514, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h15 p ha hb
theorem andIntro26727 (p : Pattern) (ha : d144473 p = 1) (hb : d145520 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d144468 q = 1) (hb : d145515 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d144468, d145515, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26726 q ha hb
    | true =>
      simp only [d144468, d145515, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d144469 q = 1) (hb : d145516 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d144469, d145516, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d144469, d145516, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d144412 q = 1) (hb : d145472 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d144412, d145472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26716 q ha hb
    | true =>
      simp only [d144412, d145472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d144413 q = 1) (hb : d145473 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d144413, d145473, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d144413, d145473, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d144470 q = 1) (hb : d145517 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d144470, d145517, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d144470, d145517, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d144471 q = 1) (hb : d145518 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d144471, d145518, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d144471, d145518, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d144472 q = 1) (hb : d145519 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d144472, d145519, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d144472, d145519, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d144473 q = 1) (hb : d145520 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d144473, d145520, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d144473, d145520, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro26728 (p : Pattern) (ha : d52431 p = 1) (hb : d145523 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d52431 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d5451 q = 1) (hb : d52428 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d5451, d52428, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro15003 q ha hb
    | true =>
      simp only [d5451, d52428, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d5452 q = 1) (hb : d52429 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d5452, d52429, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d5452, d52429, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h4 (q : Pattern) (ha : d5453 q = 1) (hb : d52430 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d5453, d52430, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d5453, d52430, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d5454 q = 1) (hb : d52431 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d5454, d52431, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d5454, d52431, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h6 (q : Pattern) (ha : d5455 q = 1) (hb : d52431 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d5455, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d5455, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d52431 q = 1) (hb : d145523 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d145523, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d145523, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  exact h7 p ha hb
theorem andIntro26729 (p : Pattern) (ha : d144411 p = 1) (hb : d145529 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d52431 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d144402 q = 1) (hb : d145374 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d144402, d145374, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26687 q ha hb
    | true =>
      simp only [d144402, d145374, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d144403 q = 1) (hb : d145375 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d144403, d145375, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d144403, d145375, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d144404 q = 1) (hb : d145376 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d144404, d145376, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d144404, d145376, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d120397 q = 1) (hb : d144405 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d120397, d144405, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26706 q hb ha
    | true =>
      simp only [d120397, d144405, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d120398 q = 1) (hb : d144406 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d120398, d144406, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d120398, d144406, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d120399 q = 1) (hb : d144407 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d120399, d144407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d120399, d144407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d144408 q = 1) (hb : d145469 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d144408, d145469, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d144408, d145469, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
  have h9 (q : Pattern) (ha : d144405 q = 1) (hb : d145524 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d144405, d145524, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26728 q ha hb
    | true =>
      simp only [d144405, d145524, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h10 (q : Pattern) (ha : d144406 q = 1) (hb : d145525 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d144406, d145525, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d144406, d145525, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d144407 q = 1) (hb : d145526 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d144407, d145526, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d144407, d145526, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d144409 q = 1) (hb : d145527 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d144409, d145527, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d144409, d145527, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d144410 q = 1) (hb : d145528 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d144410, d145528, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d144410, d145528, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d144411 q = 1) (hb : d145529 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d144411, d145529, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d144411, d145529, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h14 p ha hb
theorem andIntro26730 (p : Pattern) (ha : d144479 p = 1) (hb : d145535 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d144412 q = 1) (hb : d145530 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d144412, d145530, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26729 q ha hb
    | true =>
      simp only [d144412, d145530, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d144413 q = 1) (hb : d145531 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d144413, d145531, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d144413, d145531, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d144476 q = 1) (hb : d145532 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d144476, d145532, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d144476, d145532, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d144477 q = 1) (hb : d145533 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d144477, d145533, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d144477, d145533, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d144478 q = 1) (hb : d145534 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d144478, d145534, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d144478, d145534, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d144479 q = 1) (hb : d145535 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d144479, d145535, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d144479, d145535, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro26731 (p : Pattern) (ha : d144485 p = 1) (hb : d145541 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d144449 q = 1) (hb : d145498 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d144449, d145498, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26723 q ha hb
    | true =>
      simp only [d144449, d145498, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26721 q hb ha
  have h2 (q : Pattern) (ha : d144450 q = 1) (hb : d145499 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d144450, d145499, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d144450, d145499, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d144451 q = 1) (hb : d145500 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d144451, d145500, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d144451, d145500, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d144452 q = 1) (hb : d145501 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d144452, d145501, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d144452, d145501, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d144459 q = 1) (hb : d145505 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d144459, d145505, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26724 q ha hb
    | true =>
      simp only [d144459, d145505, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26722 q hb ha
  have h6 (q : Pattern) (ha : d144460 q = 1) (hb : d145506 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d144460, d145506, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d144460, d145506, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d144461 q = 1) (hb : d145507 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d144461, d145507, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d144461, d145507, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d144474 q = 1) (hb : d145521 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d144474, d145521, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26727 q ha hb
    | true =>
      simp only [d144474, d145521, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26717 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d144426 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d144475 q = 1) (hb : d145522 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d144475, d145522, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d144475, d145522, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
  have h11 (q : Pattern) (ha : d144480 q = 1) (hb : d145536 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d144480, d145536, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26730 q ha hb
    | true =>
      simp only [d144480, d145536, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d144481 q = 1) (hb : d145537 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d144481, d145537, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d144481, d145537, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d144482 q = 1) (hb : d145538 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d144482, d145538, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d144482, d145538, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d144483 q = 1) (hb : d145539 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d144483, d145539, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d144483, d145539, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d144484 q = 1) (hb : d145540 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d144484, d145540, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d144484, d145540, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d144485 q = 1) (hb : d145541 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d144485, d145541, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d144485, d145541, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  exact h16 p ha hb
theorem andIntro26732 (p : Pattern) (ha : d120487 p = 1) (hb : d144487 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d120407 q = 1) (hb : d144416 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d120407, d144416, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26707 q ha hb
    | true =>
      simp only [d120407, d144416, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d120408 q = 1) (hb : d144417 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d120408, d144417, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d120408, d144417, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d120413 q = 1) (hb : d144422 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d120413, d144422, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d120413, d144422, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d120414 q = 1) (hb : d144423 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d120414, d144423, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d120414, d144423, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d120438 q = 1) (hb : d144447 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d120438, d144447, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d120438, d144447, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d120487 q = 1) (hb : d144487 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d120487, d144487, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d120487, d144487, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro26733 (p : Pattern) (ha : d120493 p = 1) (hb : d144493 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d120407 q = 1) (hb : d144416 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d120407, d144416, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26707 q ha hb
    | true =>
      simp only [d120407, d144416, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d120408 q = 1) (hb : d144417 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d120408, d144417, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d120408, d144417, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d120413 q = 1) (hb : d144422 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d120413, d144422, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d120413, d144422, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d120447 q = 1) (hb : d144456 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d120447, d144456, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d120447, d144456, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d120448 q = 1) (hb : d144457 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d120448, d144457, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d120448, d144457, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d120493 q = 1) (hb : d144493 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d120493, d144493, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d120493, d144493, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro26734 (p : Pattern) (ha : d144486 p = 1) (hb : d145542 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d144412 q = 1) (hb : d145472 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d144412, d145472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26716 q ha hb
    | true =>
      simp only [d144412, d145472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d144413 q = 1) (hb : d145473 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d144413, d145473, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d144413, d145473, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d120407 q = 1) (hb : d144416 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d120407, d144416, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26707 q ha hb
    | true =>
      simp only [d120407, d144416, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d120408 q = 1) (hb : d144417 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d120408, d144417, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d120408, d144417, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d144418 q = 1) (hb : d145474 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d144418, d145474, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d144418, d145474, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d144419 q = 1) (hb : d145475 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d144419, d145475, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d144419, d145475, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d144445 q = 1) (hb : d145496 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d144445, d145496, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d144445, d145496, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d144486 q = 1) (hb : d145542 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d144486, d145542, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d144486, d145542, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro26735 (p : Pattern) (ha : d144492 p = 1) (hb : d145547 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d144412 q = 1) (hb : d145472 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d144412, d145472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26716 q ha hb
    | true =>
      simp only [d144412, d145472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d144413 q = 1) (hb : d145473 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d144413, d145473, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d144413, d145473, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d120407 q = 1) (hb : d144416 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d120407, d144416, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26707 q ha hb
    | true =>
      simp only [d120407, d144416, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d120408 q = 1) (hb : d144417 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d120408, d144417, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d120408, d144417, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d144418 q = 1) (hb : d145474 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d144418, d145474, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d144418, d145474, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d144453 q = 1) (hb : d145502 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d144453, d145502, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d144453, d145502, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d144454 q = 1) (hb : d145503 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d144454, d145503, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d144454, d145503, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d144492 q = 1) (hb : d145547 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d144492, d145547, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d144492, d145547, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro26736 (p : Pattern) (ha : d144497 p = 1) (hb : d145551 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d144468 q = 1) (hb : d145515 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d144468, d145515, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26726 q ha hb
    | true =>
      simp only [d144468, d145515, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d144469 q = 1) (hb : d145516 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d144469, d145516, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d144469, d145516, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d144412 q = 1) (hb : d145472 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d144412, d145472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26716 q ha hb
    | true =>
      simp only [d144412, d145472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d144413 q = 1) (hb : d145473 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d144413, d145473, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d144413, d145473, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d144470 q = 1) (hb : d145517 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d144470, d145517, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d144470, d145517, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d144471 q = 1) (hb : d145518 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d144471, d145518, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d144471, d145518, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d144472 q = 1) (hb : d145519 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d144472, d145519, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d144472, d145519, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d144497 q = 1) (hb : d145551 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d144497, d145551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d144497, d145551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro26737 (p : Pattern) (ha : d144500 p = 1) (hb : d145554 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d144412 q = 1) (hb : d145530 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d144412, d145530, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26729 q ha hb
    | true =>
      simp only [d144412, d145530, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d144413 q = 1) (hb : d145531 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d144413, d145531, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d144413, d145531, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d144476 q = 1) (hb : d145532 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d144476, d145532, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d144476, d145532, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d144477 q = 1) (hb : d145533 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d144477, d145533, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d144477, d145533, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d144478 q = 1) (hb : d145534 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d144478, d145534, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d144478, d145534, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d144500 q = 1) (hb : d145554 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d144500, d145554, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d144500, d145554, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro26738 (p : Pattern) (ha : d144506 p = 1) (hb : d145560 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d144449 q = 1) (hb : d145498 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d144449, d145498, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26723 q ha hb
    | true =>
      simp only [d144449, d145498, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26721 q hb ha
  have h2 (q : Pattern) (ha : d144450 q = 1) (hb : d145499 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d144450, d145499, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d144450, d145499, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d144451 q = 1) (hb : d145500 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d144451, d145500, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d144451, d145500, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d144452 q = 1) (hb : d145501 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d144452, d145501, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d144452, d145501, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d144459 q = 1) (hb : d145505 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d144459, d145505, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26724 q ha hb
    | true =>
      simp only [d144459, d145505, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26722 q hb ha
  have h6 (q : Pattern) (ha : d144460 q = 1) (hb : d145506 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d144460, d145506, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d144460, d145506, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d144461 q = 1) (hb : d145507 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d144461, d145507, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d144461, d145507, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d144474 q = 1) (hb : d145521 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d144474, d145521, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26727 q ha hb
    | true =>
      simp only [d144474, d145521, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26717 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d144426 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d144475 q = 1) (hb : d145522 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d144475, d145522, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d144475, d145522, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
  have h11 (q : Pattern) (ha : d144480 q = 1) (hb : d145536 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d144480, d145536, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26730 q ha hb
    | true =>
      simp only [d144480, d145536, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d144481 q = 1) (hb : d145537 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d144481, d145537, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d144481, d145537, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d144482 q = 1) (hb : d145538 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d144482, d145538, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d144482, d145538, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d144483 q = 1) (hb : d145539 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d144483, d145539, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d144483, d145539, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d144484 q = 1) (hb : d145540 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d144484, d145540, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d144484, d145540, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d144488 q = 1) (hb : d145543 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d144488, d145543, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26734 q ha hb
    | true =>
      simp only [d144488, d145543, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26732 q hb ha
  have h17 (q : Pattern) (ha : d144489 q = 1) (hb : d145544 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d144489, d145544, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d144489, d145544, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d144490 q = 1) (hb : d145545 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d144490, d145545, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d144490, d145545, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h19 (q : Pattern) (ha : d144491 q = 1) (hb : d145546 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d144491, d145546, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d144491, d145546, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d144494 q = 1) (hb : d145548 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d144494, d145548, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26735 q ha hb
    | true =>
      simp only [d144494, d145548, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26733 q hb ha
  have h21 (q : Pattern) (ha : d144495 q = 1) (hb : d145549 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d144495, d145549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d144495, d145549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
  have h22 (q : Pattern) (ha : d144496 q = 1) (hb : d145550 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d144496, d145550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d144496, d145550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h23 (q : Pattern) (ha : d144498 q = 1) (hb : d145552 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d144498, d145552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26736 q ha hb
    | true =>
      simp only [d144498, d145552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26719 q ha hb
  have h24 (q : Pattern) (ha : d0 q = 1) (hb : d144436 q = 1) : d0 q = 1 := by
    exact ha
  have h25 (q : Pattern) (ha : d144499 q = 1) (hb : d145553 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d144499, d145553, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
    | true =>
      simp only [d144499, d145553, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q hb ha
  have h26 (q : Pattern) (ha : d144501 q = 1) (hb : d145555 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d144501, d145555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26737 q ha hb
    | true =>
      simp only [d144501, d145555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h27 (q : Pattern) (ha : d144502 q = 1) (hb : d145556 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d144502, d145556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h26 q ha hb
    | true =>
      simp only [d144502, d145556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h28 (q : Pattern) (ha : d144503 q = 1) (hb : d145557 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d144503, d145557, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q ha hb
    | true =>
      simp only [d144503, d145557, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h27 q ha hb
  have h29 (q : Pattern) (ha : d144504 q = 1) (hb : d145558 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d144504, d145558, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
    | true =>
      simp only [d144504, d145558, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h28 q ha hb
  have h30 (q : Pattern) (ha : d144505 q = 1) (hb : d145559 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d144505, d145559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d144505, d145559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h29 q ha hb
  have h31 (q : Pattern) (ha : d144506 q = 1) (hb : d145560 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d144506, d145560, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d144506, d145560, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h30 q ha hb
  exact h31 p ha hb
theorem andIntro26739 (p : Pattern) (ha : d144513 p = 1) (hb : d145562 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d144426 q = 1) (hb : d145478 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d144426, d145478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26717 q ha hb
    | true =>
      simp only [d144426, d145478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26708 q hb ha
  have h2 (q : Pattern) (ha : d144427 q = 1) (hb : d145479 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d144427, d145479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d144427, d145479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d144428 q = 1) (hb : d145480 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d144428, d145480, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d144428, d145480, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d144429 q = 1) (hb : d145481 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d144429, d145481, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d144429, d145481, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d144430 q = 1) (hb : d145482 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d144430, d145482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d144430, d145482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d120514 q = 1) (hb : d144508 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d120514, d144508, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26708 q ha hb
    | true =>
      simp only [d120514, d144508, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d120515 q = 1) (hb : d144509 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d120515, d144509, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d120515, d144509, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d120516 q = 1) (hb : d144510 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d120516, d144510, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d120516, d144510, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d120517 q = 1) (hb : d144511 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d120517, d144511, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d120517, d144511, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d120518 q = 1) (hb : d144512 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d120518, d144512, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d120518, d144512, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d144513 q = 1) (hb : d145562 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d144513, d145562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d144513, d145562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
  exact h11 p ha hb
theorem andIntro26740 (p : Pattern) (ha : d144526 p = 1) (hb : d145569 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d144498 q = 1) (hb : d145552 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d144498, d145552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26736 q ha hb
    | true =>
      simp only [d144498, d145552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26719 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d144436 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d144499 q = 1) (hb : d145553 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d144499, d145553, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d144499, d145553, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d144501 q = 1) (hb : d145555 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d144501, d145555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26737 q ha hb
    | true =>
      simp only [d144501, d145555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d144502 q = 1) (hb : d145556 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d144502, d145556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d144502, d145556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d144503 q = 1) (hb : d145557 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d144503, d145557, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d144503, d145557, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d144524 q = 1) (hb : d145567 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d144524, d145567, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d144524, d145567, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d144525 q = 1) (hb : d145568 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d144525, d145568, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d144525, d145568, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d144526 q = 1) (hb : d145569 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d144526, d145569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d144526, d145569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro26741 (p : Pattern) (ha : d52366 p = 1) (hb : d145575 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d52366 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d659 q = 1) (hb : d52363 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d659, d52363, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d659, d52363, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro76 q ha hb
  have h3 (q : Pattern) (ha : d543 q = 1) (hb : d52290 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d543, d52290, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro76 q ha hb
    | true =>
      simp only [d543, d52290, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h4 (q : Pattern) (ha : d660 q = 1) (hb : d52364 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d660, d52364, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d660, d52364, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d544 q = 1) (hb : d52291 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d544, d52291, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d544, d52291, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h6 (q : Pattern) (ha : d661 q = 1) (hb : d52365 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d661, d52365, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d661, d52365, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d662 q = 1) (hb : d52366 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d662, d52366, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d662, d52366, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h8 (q : Pattern) (ha : d14370 q = 1) (hb : d52366 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d14370, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d14370, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d52366 q = 1) (hb : d145575 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d145575, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d145575, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  exact h9 p ha hb
theorem andIntro26742 (p : Pattern) (ha : d144546 p = 1) (hb : d145582 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d52181 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d144534 q = 1) (hb : d145576 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d144534, d145576, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26741 q ha hb
    | true =>
      simp only [d144534, d145576, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d144535 q = 1) (hb : d145577 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d144535, d145577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d144535, d145577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d144536 q = 1) (hb : d145578 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d144536, d145578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d144536, d145578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d52593 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d144537 q = 1) (hb : d145432 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d144537, d145432, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26699 q ha hb
    | true =>
      simp only [d144537, d145432, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d144538 q = 1) (hb : d145433 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d144538, d145433, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d144538, d145433, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d144539 q = 1) (hb : d145434 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d144539, d145434, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d144539, d145434, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d144540 q = 1) (hb : d145579 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d144540, d145579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d144540, d145579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d120562 q = 1) (hb : d144541 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d120562, d144541, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26712 q hb ha
    | true =>
      simp only [d120562, d144541, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d120563 q = 1) (hb : d144542 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d120563, d144542, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d120563, d144542, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d120564 q = 1) (hb : d144543 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d120564, d144543, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d120564, d144543, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d144544 q = 1) (hb : d145580 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d144544, d145580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d144544, d145580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
  have h14 (q : Pattern) (ha : d144545 q = 1) (hb : d145581 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d144545, d145581, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d144545, d145581, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d144546 q = 1) (hb : d145582 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d144546, d145582, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d144546, d145582, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h15 p ha hb
theorem andIntro26743 (p : Pattern) (ha : d144551 p = 1) (hb : d145586 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d52593 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d144537 q = 1) (hb : d145432 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d144537, d145432, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26699 q ha hb
    | true =>
      simp only [d144537, d145432, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d144538 q = 1) (hb : d145433 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d144538, d145433, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d144538, d145433, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d144539 q = 1) (hb : d145434 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d144539, d145434, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d144539, d145434, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d120562 q = 1) (hb : d144541 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d120562, d144541, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26712 q hb ha
    | true =>
      simp only [d120562, d144541, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d120563 q = 1) (hb : d144542 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d120563, d144542, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d120563, d144542, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d120564 q = 1) (hb : d144543 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d120564, d144543, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d120564, d144543, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d144544 q = 1) (hb : d145580 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d144544, d145580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d144544, d145580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
  have h9 (q : Pattern) (ha : d120565 q = 1) (hb : d144549 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d120565, d144549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d120565, d144549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d144550 q = 1) (hb : d145585 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d144550, d145585, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d144550, d145585, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
  have h11 (q : Pattern) (ha : d144551 q = 1) (hb : d145586 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d144551, d145586, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d144551, d145586, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h11 p ha hb
theorem andIntro26744 (p : Pattern) (ha : d144557 p = 1) (hb : d145592 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d144547 q = 1) (hb : d145583 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d144547, d145583, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26742 q ha hb
    | true =>
      simp only [d144547, d145583, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d144548 q = 1) (hb : d145584 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d144548, d145584, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d144548, d145584, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d144552 q = 1) (hb : d145587 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d144552, d145587, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26743 q ha hb
    | true =>
      simp only [d144552, d145587, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d144553 q = 1) (hb : d145588 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d144553, d145588, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d144553, d145588, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d144554 q = 1) (hb : d145589 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d144554, d145589, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d144554, d145589, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d144555 q = 1) (hb : d145590 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d144555, d145590, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d144555, d145590, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d144556 q = 1) (hb : d145591 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d144556, d145591, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d144556, d145591, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d144557 q = 1) (hb : d145592 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d144557, d145592, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d144557, d145592, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro26745 (p : Pattern) (ha : d144565 p = 1) (hb : d145596 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d144552 q = 1) (hb : d145587 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d144552, d145587, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26743 q ha hb
    | true =>
      simp only [d144552, d145587, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d144553 q = 1) (hb : d145588 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d144553, d145588, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d144553, d145588, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d120568 q = 1) (hb : d144560 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d120568, d144560, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26713 q ha hb
    | true =>
      simp only [d120568, d144560, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d120569 q = 1) (hb : d144561 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d120569, d144561, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d120569, d144561, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d144562 q = 1) (hb : d145593 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d144562, d145593, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d144562, d145593, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d144563 q = 1) (hb : d145594 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d144563, d145594, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d144563, d145594, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d144564 q = 1) (hb : d145595 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d144564, d145595, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d144564, d145595, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d144565 q = 1) (hb : d145596 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d144565, d145596, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d144565, d145596, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro26746 (p : Pattern) (ha : d52593 p = 1) (hb : d145599 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d52593 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d5495 q = 1) (hb : d52590 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d5495, d52590, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d5495, d52590, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro15003 q ha hb
  have h3 (q : Pattern) (ha : d5451 q = 1) (hb : d52428 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d5451, d52428, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro15003 q ha hb
    | true =>
      simp only [d5451, d52428, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h4 (q : Pattern) (ha : d5496 q = 1) (hb : d52591 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d5496, d52591, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d5496, d52591, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d5452 q = 1) (hb : d52429 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d5452, d52429, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d5452, d52429, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h6 (q : Pattern) (ha : d5497 q = 1) (hb : d52592 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d5497, d52592, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d5497, d52592, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d5498 q = 1) (hb : d52593 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d5498, d52593, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d5498, d52593, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h8 (q : Pattern) (ha : d5499 q = 1) (hb : d52593 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d5499, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d5499, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d52593 q = 1) (hb : d145599 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d145599, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d145599, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  exact h9 p ha hb
theorem andIntro26747 (p : Pattern) (ha : d144551 p = 1) (hb : d145605 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d52593 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d144537 q = 1) (hb : d145432 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d144537, d145432, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26699 q ha hb
    | true =>
      simp only [d144537, d145432, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d144538 q = 1) (hb : d145433 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d144538, d145433, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d144538, d145433, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d144539 q = 1) (hb : d145434 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d144539, d145434, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d144539, d145434, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d120562 q = 1) (hb : d144541 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d120562, d144541, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26712 q hb ha
    | true =>
      simp only [d120562, d144541, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d120563 q = 1) (hb : d144542 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d120563, d144542, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d120563, d144542, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d120564 q = 1) (hb : d144543 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d120564, d144543, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d120564, d144543, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d144544 q = 1) (hb : d145580 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d144544, d145580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d144544, d145580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
  have h9 (q : Pattern) (ha : d144541 q = 1) (hb : d145600 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d144541, d145600, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26746 q ha hb
    | true =>
      simp only [d144541, d145600, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h10 (q : Pattern) (ha : d144542 q = 1) (hb : d145601 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d144542, d145601, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d144542, d145601, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d144543 q = 1) (hb : d145602 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d144543, d145602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d144543, d145602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d144549 q = 1) (hb : d145603 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d144549, d145603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d144549, d145603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d144550 q = 1) (hb : d145604 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d144550, d145604, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d144550, d145604, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d144551 q = 1) (hb : d145605 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d144551, d145605, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d144551, d145605, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h14 p ha hb
theorem andIntro26748 (p : Pattern) (ha : d144576 p = 1) (hb : d145611 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d144552 q = 1) (hb : d145606 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d144552, d145606, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26747 q ha hb
    | true =>
      simp only [d144552, d145606, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d144553 q = 1) (hb : d145607 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d144553, d145607, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d144553, d145607, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d144573 q = 1) (hb : d145608 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d144573, d145608, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d144573, d145608, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d144574 q = 1) (hb : d145609 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d144574, d145609, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d144574, d145609, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d144575 q = 1) (hb : d145610 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d144575, d145610, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d144575, d145610, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d144576 q = 1) (hb : d145611 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d144576, d145611, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d144576, d145611, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro26749 (p : Pattern) (ha : d144582 p = 1) (hb : d145617 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d144566 q = 1) (hb : d145597 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d144566, d145597, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26744 q ha hb
    | true =>
      simp only [d144566, d145597, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26745 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d144571 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d144572 q = 1) (hb : d145598 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d144572, d145598, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d144572, d145598, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d144577 q = 1) (hb : d145612 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d144577, d145612, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26748 q ha hb
    | true =>
      simp only [d144577, d145612, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d144578 q = 1) (hb : d145613 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d144578, d145613, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d144578, d145613, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d144579 q = 1) (hb : d145614 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d144579, d145614, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d144579, d145614, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d144580 q = 1) (hb : d145615 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d144580, d145615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d144580, d145615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d144581 q = 1) (hb : d145616 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d144581, d145616, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d144581, d145616, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d144582 q = 1) (hb : d145617 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d144582, d145617, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d144582, d145617, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
end NetHack.Soko22Hazard87
