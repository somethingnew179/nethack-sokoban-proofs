import NetHack.Soko22Hazard87.AndIntroBlocks0124
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Soko22Hazard87
open NetHack.Sokoban NetHack.Sokoban.PatternCorrection
theorem andIntro31250 (p : Pattern) (ha : d123687 p = 1) (hb : d159417 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d123606 q = 1) (hb : d159355 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d123606, d159355, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31235 q ha hb
    | true =>
      simp only [d123606, d159355, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22363 q ha hb
  have h2 (q : Pattern) (ha : d123607 q = 1) (hb : d159356 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d123607, d159356, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123607, d159356, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d123608 q = 1) (hb : d159357 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d123608, d159357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d123608, d159357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d123609 q = 1) (hb : d159358 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d123609, d159358, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123609, d159358, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d123616 q = 1) (hb : d159362 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d123616, d159362, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31236 q ha hb
    | true =>
      simp only [d123616, d159362, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22365 q ha hb
  have h6 (q : Pattern) (ha : d123617 q = 1) (hb : d159363 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d123617, d159363, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123617, d159363, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d123618 q = 1) (hb : d159364 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d123618, d159364, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d123618, d159364, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d123646 q = 1) (hb : d159386 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d123646, d159386, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31240 q ha hb
    | true =>
      simp only [d123646, d159386, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31241 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d123583 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d123647 q = 1) (hb : d159387 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d123647, d159387, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d123647, d159387, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
  have h11 (q : Pattern) (ha : d123660 q = 1) (hb : d159392 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d123660, d159392, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31243 q ha hb
    | true =>
      simp only [d123660, d159392, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d123661 q = 1) (hb : d159393 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d123661, d159393, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d123661, d159393, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d123662 q = 1) (hb : d159394 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d123662, d159394, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d123662, d159394, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d123663 q = 1) (hb : d159395 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d123663, d159395, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d123663, d159395, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d123664 q = 1) (hb : d159396 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d123664, d159396, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d123664, d159396, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d123668 q = 1) (hb : d159399 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d123668, d159399, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31245 q ha hb
    | true =>
      simp only [d123668, d159399, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22376 q ha hb
  have h17 (q : Pattern) (ha : d123669 q = 1) (hb : d159400 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d123669, d159400, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123669, d159400, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d123670 q = 1) (hb : d159401 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d123670, d159401, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d123670, d159401, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h19 (q : Pattern) (ha : d123671 q = 1) (hb : d159402 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d123671, d159402, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123671, d159402, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d123674 q = 1) (hb : d159404 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d123674, d159404, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31246 q ha hb
    | true =>
      simp only [d123674, d159404, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22378 q ha hb
  have h21 (q : Pattern) (ha : d123675 q = 1) (hb : d159405 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d123675, d159405, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123675, d159405, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
  have h22 (q : Pattern) (ha : d123676 q = 1) (hb : d159406 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d123676, d159406, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d123676, d159406, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h23 (q : Pattern) (ha : d123679 q = 1) (hb : d159409 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d123679, d159409, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31247 q ha hb
    | true =>
      simp only [d123679, d159409, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31248 q ha hb
  have h24 (q : Pattern) (ha : d0 q = 1) (hb : d123593 q = 1) : d0 q = 1 := by
    exact ha
  have h25 (q : Pattern) (ha : d123680 q = 1) (hb : d159410 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d123680, d159410, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
    | true =>
      simp only [d123680, d159410, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q hb ha
  have h26 (q : Pattern) (ha : d123682 q = 1) (hb : d159412 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d123682, d159412, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31249 q ha hb
    | true =>
      simp only [d123682, d159412, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h27 (q : Pattern) (ha : d123683 q = 1) (hb : d159413 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d123683, d159413, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h26 q ha hb
    | true =>
      simp only [d123683, d159413, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h28 (q : Pattern) (ha : d123684 q = 1) (hb : d159414 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d123684, d159414, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q ha hb
    | true =>
      simp only [d123684, d159414, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h27 q ha hb
  have h29 (q : Pattern) (ha : d123685 q = 1) (hb : d159415 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d123685, d159415, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
    | true =>
      simp only [d123685, d159415, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h28 q ha hb
  have h30 (q : Pattern) (ha : d123686 q = 1) (hb : d159416 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d123686, d159416, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d123686, d159416, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h29 q ha hb
  have h31 (q : Pattern) (ha : d123687 q = 1) (hb : d159417 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d123687, d159417, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d123687, d159417, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h30 q ha hb
  exact h31 p ha hb
theorem andIntro31251 (p : Pattern) (ha : d123699 p = 1) (hb : d159424 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d123689 q = 1) (hb : d159419 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d123689, d159419, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31241 q ha hb
    | true =>
      simp only [d123689, d159419, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22357 q ha hb
  have h2 (q : Pattern) (ha : d123690 q = 1) (hb : d159420 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d123690, d159420, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123690, d159420, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d123691 q = 1) (hb : d159421 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d123691, d159421, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d123691, d159421, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d123692 q = 1) (hb : d159422 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d123692, d159422, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123692, d159422, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d123693 q = 1) (hb : d159423 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d123693, d159423, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123693, d159423, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d123694 q = 1) (hb : d125037 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d123694, d125037, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22357 q ha hb
    | true =>
      simp only [d123694, d125037, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d123695 q = 1) (hb : d125038 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d123695, d125038, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123695, d125038, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d123696 q = 1) (hb : d125039 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d123696, d125039, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d123696, d125039, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d123697 q = 1) (hb : d125040 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d123697, d125040, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123697, d125040, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d123698 q = 1) (hb : d125041 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d123698, d125041, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123698, d125041, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d123699 q = 1) (hb : d159424 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d123699, d159424, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d123699, d159424, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro31252 (p : Pattern) (ha : d123712 p = 1) (hb : d159431 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d123679 q = 1) (hb : d159409 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d123679, d159409, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31247 q ha hb
    | true =>
      simp only [d123679, d159409, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31248 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d123593 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d123680 q = 1) (hb : d159410 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d123680, d159410, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d123680, d159410, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d123682 q = 1) (hb : d159412 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d123682, d159412, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31249 q ha hb
    | true =>
      simp only [d123682, d159412, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d123683 q = 1) (hb : d159413 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d123683, d159413, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d123683, d159413, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d123684 q = 1) (hb : d159414 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d123684, d159414, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d123684, d159414, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d123710 q = 1) (hb : d159429 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d123710, d159429, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123710, d159429, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d123711 q = 1) (hb : d159430 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d123711, d159430, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123711, d159430, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d123712 q = 1) (hb : d159431 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d123712, d159431, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123712, d159431, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro31253 (p : Pattern) (ha : d123733 p = 1) (hb : d159437 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d13813 q = 1) (hb : d113965 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d13813, d113965, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13813, d113965, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23367 q ha hb
  have h2 (q : Pattern) (ha : d10353 q = 1) (hb : d101674 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d10353, d101674, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23367 q ha hb
    | true =>
      simp only [d10353, d101674, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d13814 q = 1) (hb : d113966 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d13814, d113966, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d13814, d113966, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d10355 q = 1) (hb : d101676 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d10355, d101676, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d10355, d101676, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d13815 q = 1) (hb : d113967 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d13815, d113967, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d13815, d113967, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d13816 q = 1) (hb : d113968 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d13816, d113968, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d13816, d113968, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d15770 q = 1) (hb : d123723 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d15770, d123723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d15770, d123723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d123732 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d123733 q = 1) (hb : d159437 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d123733, d159437, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
    | true =>
      simp only [d123733, d159437, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  exact h9 p ha hb
theorem andIntro31254 (p : Pattern) (ha : d123754 p = 1) (hb : d159444 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d123725 q = 1) (hb : d125064 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d123725, d125064, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22387 q hb ha
    | true =>
      simp only [d123725, d125064, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22388 q ha hb
  have h2 (q : Pattern) (ha : d123726 q = 1) (hb : d125065 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d123726, d125065, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123726, d125065, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d123727 q = 1) (hb : d125066 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d123727, d125066, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123727, d125066, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d123734 q = 1) (hb : d159438 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d123734, d159438, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22388 q ha hb
    | true =>
      simp only [d123734, d159438, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31253 q ha hb
  have h5 (q : Pattern) (ha : d123735 q = 1) (hb : d159439 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d123735, d159439, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123735, d159439, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d123736 q = 1) (hb : d159440 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d123736, d159440, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123736, d159440, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d123737 q = 1) (hb : d159441 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d123737, d159441, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d123737, d159441, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d123740 q = 1) (hb : d125069 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d123740, d125069, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22388 q ha hb
    | true =>
      simp only [d123740, d125069, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22389 q ha hb
  have h9 (q : Pattern) (ha : d123741 q = 1) (hb : d125070 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d123741, d125070, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123741, d125070, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d123742 q = 1) (hb : d125071 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d123742, d125071, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123742, d125071, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d123749 q = 1) (hb : d125077 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d123749, d125077, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22389 q ha hb
    | true =>
      simp only [d123749, d125077, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22391 q hb ha
  have h12 (q : Pattern) (ha : d123750 q = 1) (hb : d125078 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d123750, d125078, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123750, d125078, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d123751 q = 1) (hb : d125079 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d123751, d125079, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123751, d125079, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d123752 q = 1) (hb : d159442 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d123752, d159442, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d123752, d159442, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d123753 q = 1) (hb : d159443 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d123753, d159443, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d123753, d159443, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d123754 q = 1) (hb : d159444 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d123754, d159444, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d123754, d159444, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h16 p ha hb
theorem andIntro31255 (p : Pattern) (ha : d123759 p = 1) (hb : d159448 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d123740 q = 1) (hb : d125069 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d123740, d125069, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22388 q ha hb
    | true =>
      simp only [d123740, d125069, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22389 q ha hb
  have h2 (q : Pattern) (ha : d123741 q = 1) (hb : d125070 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d123741, d125070, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123741, d125070, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d123742 q = 1) (hb : d125071 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d123742, d125071, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123742, d125071, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d123749 q = 1) (hb : d125077 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d123749, d125077, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22389 q ha hb
    | true =>
      simp only [d123749, d125077, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22391 q hb ha
  have h5 (q : Pattern) (ha : d123750 q = 1) (hb : d125078 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d123750, d125078, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123750, d125078, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d123751 q = 1) (hb : d125079 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d123751, d125079, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123751, d125079, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d123752 q = 1) (hb : d159442 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d123752, d159442, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d123752, d159442, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d123757 q = 1) (hb : d125080 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d123757, d125080, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d123757, d125080, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d123758 q = 1) (hb : d159447 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d123758, d159447, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d123758, d159447, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d123759 q = 1) (hb : d159448 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d123759, d159448, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d123759, d159448, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h10 p ha hb
theorem andIntro31256 (p : Pattern) (ha : d123765 p = 1) (hb : d159454 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d123755 q = 1) (hb : d159445 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d123755, d159445, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31254 q ha hb
    | true =>
      simp only [d123755, d159445, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d123756 q = 1) (hb : d159446 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d123756, d159446, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123756, d159446, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d123760 q = 1) (hb : d159449 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d123760, d159449, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31255 q ha hb
    | true =>
      simp only [d123760, d159449, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d123761 q = 1) (hb : d159450 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d123761, d159450, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123761, d159450, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d123762 q = 1) (hb : d159451 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d123762, d159451, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d123762, d159451, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d123763 q = 1) (hb : d159452 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d123763, d159452, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d123763, d159452, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d123764 q = 1) (hb : d159453 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d123764, d159453, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d123764, d159453, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d123765 q = 1) (hb : d159454 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d123765, d159454, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d123765, d159454, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro31257 (p : Pattern) (ha : d123778 p = 1) (hb : d159458 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d123760 q = 1) (hb : d159449 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d123760, d159449, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31255 q ha hb
    | true =>
      simp only [d123760, d159449, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d123761 q = 1) (hb : d159450 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d123761, d159450, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123761, d159450, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d123773 q = 1) (hb : d125095 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d123773, d125095, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22395 q ha hb
    | true =>
      simp only [d123773, d125095, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d123774 q = 1) (hb : d125096 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d123774, d125096, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123774, d125096, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d123775 q = 1) (hb : d159455 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d123775, d159455, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d123775, d159455, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d123776 q = 1) (hb : d159456 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d123776, d159456, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d123776, d159456, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d123777 q = 1) (hb : d159457 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d123777, d159457, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d123777, d159457, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d123778 q = 1) (hb : d159458 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d123778, d159458, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d123778, d159458, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro31258 (p : Pattern) (ha : d123799 p = 1) (hb : d159462 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d123740 q = 1) (hb : d125069 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d123740, d125069, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22388 q ha hb
    | true =>
      simp only [d123740, d125069, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22389 q ha hb
  have h2 (q : Pattern) (ha : d123741 q = 1) (hb : d125070 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d123741, d125070, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123741, d125070, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d123742 q = 1) (hb : d125071 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d123742, d125071, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123742, d125071, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d123749 q = 1) (hb : d125077 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d123749, d125077, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22389 q ha hb
    | true =>
      simp only [d123749, d125077, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22391 q hb ha
  have h5 (q : Pattern) (ha : d123750 q = 1) (hb : d125078 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d123750, d125078, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123750, d125078, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d123751 q = 1) (hb : d125079 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d123751, d125079, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123751, d125079, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d123752 q = 1) (hb : d159442 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d123752, d159442, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d123752, d159442, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d123794 q = 1) (hb : d125089 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d123794, d125089, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22389 q ha hb
    | true =>
      simp only [d123794, d125089, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18736 q hb ha
  have h9 (q : Pattern) (ha : d123795 q = 1) (hb : d125090 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d123795, d125090, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123795, d125090, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d123796 q = 1) (hb : d125091 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d123796, d125091, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123796, d125091, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d123797 q = 1) (hb : d125092 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d123797, d125092, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d123797, d125092, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d123798 q = 1) (hb : d159461 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d123798, d159461, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d123798, d159461, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d123799 q = 1) (hb : d159462 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d123799, d159462, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d123799, d159462, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h13 p ha hb
theorem andIntro31259 (p : Pattern) (ha : d123805 p = 1) (hb : d159468 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d123800 q = 1) (hb : d159463 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d123800, d159463, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31258 q ha hb
    | true =>
      simp only [d123800, d159463, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d123801 q = 1) (hb : d159464 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d123801, d159464, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123801, d159464, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d123802 q = 1) (hb : d159465 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d123802, d159465, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d123802, d159465, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d123803 q = 1) (hb : d159466 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d123803, d159466, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d123803, d159466, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d123804 q = 1) (hb : d159467 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d123804, d159467, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d123804, d159467, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d123805 q = 1) (hb : d159468 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d123805, d159468, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d123805, d159468, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro31260 (p : Pattern) (ha : d123811 p = 1) (hb : d159474 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d123779 q = 1) (hb : d159459 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d123779, d159459, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31256 q ha hb
    | true =>
      simp only [d123779, d159459, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31257 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d123792 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d123793 q = 1) (hb : d159460 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d123793, d159460, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d123793, d159460, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d123806 q = 1) (hb : d159469 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d123806, d159469, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31259 q ha hb
    | true =>
      simp only [d123806, d159469, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d123807 q = 1) (hb : d159470 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d123807, d159470, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d123807, d159470, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d123808 q = 1) (hb : d159471 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d123808, d159471, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d123808, d159471, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d123809 q = 1) (hb : d159472 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d123809, d159472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123809, d159472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d123810 q = 1) (hb : d159473 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d123810, d159473, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123810, d159473, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d123811 q = 1) (hb : d159474 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d123811, d159474, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123811, d159474, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro31261 (p : Pattern) (ha : d123824 p = 1) (hb : d159480 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d123589 q = 1) (hb : d159341 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d123589, d159341, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123589, d159341, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31232 q ha hb
  have h2 (q : Pattern) (ha : d123590 q = 1) (hb : d159342 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d123590, d159342, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d123590, d159342, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d123599 q = 1) (hb : d159350 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d123599, d159350, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31232 q ha hb
    | true =>
      simp only [d123599, d159350, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31234 q ha hb
  have h4 (q : Pattern) (ha : d123600 q = 1) (hb : d159351 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d123600, d159351, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d123600, d159351, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d123601 q = 1) (hb : d159352 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d123601, d159352, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d123601, d159352, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d123688 q = 1) (hb : d159418 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d123688, d159418, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31244 q ha hb
    | true =>
      simp only [d123688, d159418, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31250 q ha hb
  have h7 (q : Pattern) (ha : d123706 q = 1) (hb : d159425 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d123706, d159425, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31251 q ha hb
    | true =>
      simp only [d123706, d159425, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22384 q ha hb
  have h8 (q : Pattern) (ha : d123707 q = 1) (hb : d159426 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d123707, d159426, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d123707, d159426, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d123708 q = 1) (hb : d159427 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d123708, d159427, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d123708, d159427, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h10 (q : Pattern) (ha : d123709 q = 1) (hb : d159428 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d123709, d159428, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d123709, d159428, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d123713 q = 1) (hb : d159432 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d123713, d159432, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123713, d159432, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31252 q ha hb
  have h12 (q : Pattern) (ha : d123715 q = 1) (hb : d125058 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d123715, d125058, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123715, d125058, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22386 q ha hb
  have h13 (q : Pattern) (ha : d123716 q = 1) (hb : d159433 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d123716, d159433, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d123716, d159433, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d123717 q = 1) (hb : d159434 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d123717, d159434, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d123717, d159434, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h15 (q : Pattern) (ha : d123718 q = 1) (hb : d159435 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d123718, d159435, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d123718, d159435, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h16 (q : Pattern) (ha : d123719 q = 1) (hb : d159436 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d123719, d159436, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d123719, d159436, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d123812 q = 1) (hb : d159475 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d123812, d159475, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123812, d159475, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31260 q ha hb
  have h18 (q : Pattern) (ha : d123819 q = 1) (hb : d125128 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d123819, d125128, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123819, d125128, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22401 q ha hb
  have h19 (q : Pattern) (ha : d123820 q = 1) (hb : d159476 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d123820, d159476, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d123820, d159476, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d123821 q = 1) (hb : d159477 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d123821, d159477, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d123821, d159477, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h21 (q : Pattern) (ha : d123822 q = 1) (hb : d159478 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d123822, d159478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d123822, d159478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h22 (q : Pattern) (ha : d123823 q = 1) (hb : d159479 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d123823, d159479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d123823, d159479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h23 (q : Pattern) (ha : d123824 q = 1) (hb : d159480 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d123824, d159480, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d123824, d159480, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
  exact h23 p ha hb
theorem andIntro31262 (p : Pattern) (ha : d123830 p = 1) (hb : d159486 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d123825 q = 1) (hb : d159481 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d123825, d159481, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123825, d159481, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31261 q ha hb
  have h2 (q : Pattern) (ha : d123826 q = 1) (hb : d159482 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d123826, d159482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123826, d159482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d123827 q = 1) (hb : d159483 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d123827, d159483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123827, d159483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d123828 q = 1) (hb : d159484 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d123828, d159484, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123828, d159484, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d123829 q = 1) (hb : d159485 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d123829, d159485, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123829, d159485, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d123830 q = 1) (hb : d159486 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d123830, d159486, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123830, d159486, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro31263 (p : Pattern) (ha : d123836 p = 1) (hb : d159492 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d122703 q = 1) (hb : d158851 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d122703, d158851, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31107 q ha hb
    | true =>
      simp only [d122703, d158851, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31135 q ha hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d122926 q = 1) (hb : d158995 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d122926, d158995, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d122926, d158995, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31163 q ha hb
  have h3 (q : Pattern) (ha : d122927 q = 1) (hb : d158996 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d122927, d158996, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d122927, d158996, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d123232 q = 1) (hb : d159158 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d123232, d159158, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d123232, d159158, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31196 q ha hb
  have h5 (q : Pattern) (ha : d123233 q = 1) (hb : d159159 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d123233, d159159, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d123233, d159159, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d123234 q = 1) (hb : d159160 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d123234, d159160, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d123234, d159160, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d123539 q = 1) (hb : d159322 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d123539, d159322, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d123539, d159322, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31229 q ha hb
  have h8 (q : Pattern) (ha : d123540 q = 1) (hb : d159323 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d123540, d159323, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d123540, d159323, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d123541 q = 1) (hb : d159324 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d123541, d159324, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d123541, d159324, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d123542 q = 1) (hb : d159325 q = 1) : d0 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d123542, d159325, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d123542, d159325, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d123831 q = 1) (hb : d159487 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d123831, d159487, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d123831, d159487, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31262 q ha hb
  have h12 (q : Pattern) (ha : d123832 q = 1) (hb : d159488 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d123832, d159488, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d123832, d159488, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d123833 q = 1) (hb : d159489 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d123833, d159489, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d123833, d159489, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d123834 q = 1) (hb : d159490 q = 1) : d0 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d123834, d159490, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d123834, d159490, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d123835 q = 1) (hb : d159491 q = 1) : d0 q = 1 := by
    cases bit : q 10250 with
    | false =>
      simp only [d123835, d159491, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d123835, d159491, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d123836 q = 1) (hb : d159492 q = 1) : d0 q = 1 := by
    cases bit : q 260 with
    | false =>
      simp only [d123836, d159492, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d123836, d159492, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  exact h16 p ha hb
theorem andIntro31264 (p : Pattern) (ha : d123842 p = 1) (hb : d159498 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d123837 q = 1) (hb : d159493 q = 1) : d0 q = 1 := by
    cases bit : q 259 with
    | false =>
      simp only [d123837, d159493, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31263 q ha hb
    | true =>
      simp only [d123837, d159493, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d123838 q = 1) (hb : d159494 q = 1) : d0 q = 1 := by
    cases bit : q 258 with
    | false =>
      simp only [d123838, d159494, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d123838, d159494, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d123839 q = 1) (hb : d159495 q = 1) : d0 q = 1 := by
    cases bit : q 257 with
    | false =>
      simp only [d123839, d159495, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d123839, d159495, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d123840 q = 1) (hb : d159496 q = 1) : d0 q = 1 := by
    cases bit : q 256 with
    | false =>
      simp only [d123840, d159496, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d123840, d159496, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d123841 q = 1) (hb : d159497 q = 1) : d0 q = 1 := by
    cases bit : q 255 with
    | false =>
      simp only [d123841, d159497, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d123841, d159497, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d123842 q = 1) (hb : d159498 q = 1) : d0 q = 1 := by
    cases bit : q 254 with
    | false =>
      simp only [d123842, d159498, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d123842, d159498, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro31265 (p : Pattern) (ha : d123848 p = 1) (hb : d159504 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d123843 q = 1) (hb : d159499 q = 1) : d0 q = 1 := by
    cases bit : q 253 with
    | false =>
      simp only [d123843, d159499, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31264 q ha hb
    | true =>
      simp only [d123843, d159499, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d123844 q = 1) (hb : d159500 q = 1) : d0 q = 1 := by
    cases bit : q 252 with
    | false =>
      simp only [d123844, d159500, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d123844, d159500, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d123845 q = 1) (hb : d159501 q = 1) : d0 q = 1 := by
    cases bit : q 251 with
    | false =>
      simp only [d123845, d159501, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d123845, d159501, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d123846 q = 1) (hb : d159502 q = 1) : d0 q = 1 := by
    cases bit : q 250 with
    | false =>
      simp only [d123846, d159502, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d123846, d159502, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d123847 q = 1) (hb : d159503 q = 1) : d0 q = 1 := by
    cases bit : q 249 with
    | false =>
      simp only [d123847, d159503, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d123847, d159503, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d123848 q = 1) (hb : d159504 q = 1) : d0 q = 1 := by
    cases bit : q 245 with
    | false =>
      simp only [d123848, d159504, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d123848, d159504, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro31266 (p : Pattern) (ha : d123854 p = 1) (hb : d159510 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d123849 q = 1) (hb : d159505 q = 1) : d0 q = 1 := by
    cases bit : q 200 with
    | false =>
      simp only [d123849, d159505, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31265 q ha hb
    | true =>
      simp only [d123849, d159505, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d123850 q = 1) (hb : d159506 q = 1) : d0 q = 1 := by
    cases bit : q 199 with
    | false =>
      simp only [d123850, d159506, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d123850, d159506, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d123851 q = 1) (hb : d159507 q = 1) : d0 q = 1 := by
    cases bit : q 186 with
    | false =>
      simp only [d123851, d159507, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d123851, d159507, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d123852 q = 1) (hb : d159508 q = 1) : d0 q = 1 := by
    cases bit : q 185 with
    | false =>
      simp only [d123852, d159508, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d123852, d159508, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d123853 q = 1) (hb : d159509 q = 1) : d0 q = 1 := by
    cases bit : q 184 with
    | false =>
      simp only [d123853, d159509, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d123853, d159509, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d123854 q = 1) (hb : d159510 q = 1) : d0 q = 1 := by
    cases bit : q 181 with
    | false =>
      simp only [d123854, d159510, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d123854, d159510, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro31267 (p : Pattern) (ha : d123860 p = 1) (hb : d159516 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d123855 q = 1) (hb : d159511 q = 1) : d0 q = 1 := by
    cases bit : q 177 with
    | false =>
      simp only [d123855, d159511, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31266 q ha hb
    | true =>
      simp only [d123855, d159511, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d123856 q = 1) (hb : d159512 q = 1) : d0 q = 1 := by
    cases bit : q 164 with
    | false =>
      simp only [d123856, d159512, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d123856, d159512, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d123857 q = 1) (hb : d159513 q = 1) : d0 q = 1 := by
    cases bit : q 156 with
    | false =>
      simp only [d123857, d159513, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d123857, d159513, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d123858 q = 1) (hb : d159514 q = 1) : d0 q = 1 := by
    cases bit : q 155 with
    | false =>
      simp only [d123858, d159514, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d123858, d159514, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d123859 q = 1) (hb : d159515 q = 1) : d0 q = 1 := by
    cases bit : q 134 with
    | false =>
      simp only [d123859, d159515, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d123859, d159515, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d123860 q = 1) (hb : d159516 q = 1) : d0 q = 1 := by
    cases bit : q 133 with
    | false =>
      simp only [d123860, d159516, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d123860, d159516, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro31268 (p : Pattern) (ha : d123866 p = 1) (hb : d159522 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d123861 q = 1) (hb : d159517 q = 1) : d0 q = 1 := by
    cases bit : q 120 with
    | false =>
      simp only [d123861, d159517, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31267 q ha hb
    | true =>
      simp only [d123861, d159517, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d123862 q = 1) (hb : d159518 q = 1) : d0 q = 1 := by
    cases bit : q 118 with
    | false =>
      simp only [d123862, d159518, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d123862, d159518, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d123863 q = 1) (hb : d159519 q = 1) : d0 q = 1 := by
    cases bit : q 114 with
    | false =>
      simp only [d123863, d159519, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d123863, d159519, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d123864 q = 1) (hb : d159520 q = 1) : d0 q = 1 := by
    cases bit : q 111 with
    | false =>
      simp only [d123864, d159520, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d123864, d159520, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d123865 q = 1) (hb : d159521 q = 1) : d0 q = 1 := by
    cases bit : q 98 with
    | false =>
      simp only [d123865, d159521, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d123865, d159521, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d123866 q = 1) (hb : d159522 q = 1) : d0 q = 1 := by
    cases bit : q 97 with
    | false =>
      simp only [d123866, d159522, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d123866, d159522, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro31269 (p : Pattern) (ha : d123872 p = 1) (hb : d159528 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d123867 q = 1) (hb : d159523 q = 1) : d0 q = 1 := by
    cases bit : q 94 with
    | false =>
      simp only [d123867, d159523, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31268 q ha hb
    | true =>
      simp only [d123867, d159523, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d123868 q = 1) (hb : d159524 q = 1) : d0 q = 1 := by
    cases bit : q 76 with
    | false =>
      simp only [d123868, d159524, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d123868, d159524, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d123869 q = 1) (hb : d159525 q = 1) : d0 q = 1 := by
    cases bit : q 67 with
    | false =>
      simp only [d123869, d159525, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d123869, d159525, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d123870 q = 1) (hb : d159526 q = 1) : d0 q = 1 := by
    cases bit : q 52 with
    | false =>
      simp only [d123870, d159526, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d123870, d159526, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d123871 q = 1) (hb : d159527 q = 1) : d0 q = 1 := by
    cases bit : q 47 with
    | false =>
      simp only [d123871, d159527, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d123871, d159527, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d123872 q = 1) (hb : d159528 q = 1) : d0 q = 1 := by
    cases bit : q 46 with
    | false =>
      simp only [d123872, d159528, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d123872, d159528, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro31270 (p : Pattern) (ha : d123878 p = 1) (hb : d159534 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d123873 q = 1) (hb : d159529 q = 1) : d0 q = 1 := by
    cases bit : q 45 with
    | false =>
      simp only [d123873, d159529, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31269 q ha hb
    | true =>
      simp only [d123873, d159529, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d123874 q = 1) (hb : d159530 q = 1) : d0 q = 1 := by
    cases bit : q 30 with
    | false =>
      simp only [d123874, d159530, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d123874, d159530, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d123875 q = 1) (hb : d159531 q = 1) : d0 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d123875, d159531, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d123875, d159531, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d123876 q = 1) (hb : d159532 q = 1) : d0 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d123876, d159532, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d123876, d159532, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d123877 q = 1) (hb : d159533 q = 1) : d0 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d123877, d159533, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d123877, d159533, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d123878 q = 1) (hb : d159534 q = 1) : d0 q = 1 := by
    cases bit : q 25 with
    | false =>
      simp only [d123878, d159534, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d123878, d159534, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro31271 (p : Pattern) (ha : d122305 p = 1) (hb : d150329 p = 1) : d159537 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122305 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d49 q = 1) (hb : d122305 q = 1) : d49 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d12241 q = 1) (hb : d122305 q = 1) : d158552 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d12241, d158552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30811 q ha hb
    | true =>
      simp only [d12241, d158552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d12292 q = 1) (hb : d122305 q = 1) : d158603 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d12292, d158603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12292, d158603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d12293 q = 1) (hb : d122305 q = 1) : d158604 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d12293, d158604, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d12293, d158604, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d12294 q = 1) (hb : d122305 q = 1) : d158605 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d12294, d158605, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12294, d158605, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d12295 q = 1) (hb : d122305 q = 1) : d158606 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d12295, d158606, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12295, d158606, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d122305 q = 1) (hb : d150329 q = 1) : d159537 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d150329, d159537, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d150329, d159537, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  exact h7 p ha hb
theorem andIntro31272 (p : Pattern) (ha : d122305 p = 1) (hb : d150339 p = 1) : d159547 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122305 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d83 q = 1) (hb : d122305 q = 1) : d83 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d12268 q = 1) (hb : d122305 q = 1) : d158579 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d12268, d158579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30815 q ha hb
    | true =>
      simp only [d12268, d158579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d122305 q = 1) (hb : d150335 q = 1) : d159543 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d150335, d159543, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d150335, d159543, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d122305 q = 1) (hb : d150336 q = 1) : d159544 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d150336, d159544, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d150336, d159544, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d122305 q = 1) (hb : d150337 q = 1) : d159545 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d150337, d159545, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d150337, d159545, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d122305 q = 1) (hb : d150338 q = 1) : d159546 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d150338, d159546, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d150338, d159546, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d122305 q = 1) (hb : d150339 q = 1) : d159547 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d150339, d159547, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d150339, d159547, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro31273 (p : Pattern) (ha : d122305 p = 1) (hb : d150345 p = 1) : d159553 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122305 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12297 q = 1) (hb : d122305 q = 1) : d158608 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d12297, d158608, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30818 q ha hb
    | true =>
      simp only [d12297, d158608, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30819 q ha hb
  have h2 (q : Pattern) (ha : d12298 q = 1) (hb : d122305 q = 1) : d158609 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d12298, d158609, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d12298, d158609, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d122305 q = 1) (hb : d150327 q = 1) : d159535 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d150327, d159535, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d150327, d159535, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d122305 q = 1) (hb : d150328 q = 1) : d159536 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d150328, d159536, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d150328, d159536, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d122305 q = 1) (hb : d150330 q = 1) : d159538 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d150330, d159538, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d150330, d159538, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31271 q ha hb
  have h6 (q : Pattern) (ha : d122305 q = 1) (hb : d150331 q = 1) : d159539 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d150331, d159539, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d150331, d159539, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d122305 q = 1) (hb : d150332 q = 1) : d159540 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d150332, d159540, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d150332, d159540, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d122305 q = 1) (hb : d150333 q = 1) : d159541 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d150333, d159541, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d150333, d159541, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d122305 q = 1) (hb : d150334 q = 1) : d159542 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d150334, d159542, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d150334, d159542, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d122305 q = 1) (hb : d150340 q = 1) : d159548 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d150340, d159548, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d150340, d159548, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31272 q ha hb
  have h11 (q : Pattern) (ha : d122305 q = 1) (hb : d150341 q = 1) : d159549 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d150341, d159549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d150341, d159549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d122305 q = 1) (hb : d150342 q = 1) : d159550 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d150342, d159550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d150342, d159550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d122305 q = 1) (hb : d150343 q = 1) : d159551 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d150343, d159551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d150343, d159551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h14 (q : Pattern) (ha : d122305 q = 1) (hb : d150344 q = 1) : d159552 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d150344, d159552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d150344, d159552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h15 (q : Pattern) (ha : d122305 q = 1) (hb : d150345 q = 1) : d159553 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d150345, d159553, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d150345, d159553, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro31274 (p : Pattern) (ha : d122305 p = 1) (hb : d150351 p = 1) : d159559 p = 1 := by
  have h0 (q : Pattern) (ha : d53652 q = 1) (hb : d122305 q = 1) : d53652 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d122305 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d122305 q = 1) (hb : d150346 q = 1) : d159554 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d150346, d159554, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d150346, d159554, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31273 q ha hb
  have h3 (q : Pattern) (ha : d122305 q = 1) (hb : d150347 q = 1) : d159555 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d150347, d159555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d150347, d159555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d122305 q = 1) (hb : d150348 q = 1) : d159556 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d150348, d159556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d150348, d159556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d122305 q = 1) (hb : d150349 q = 1) : d159557 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d150349, d159557, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d150349, d159557, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d122305 q = 1) (hb : d150350 q = 1) : d159558 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d150350, d159558, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d150350, d159558, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d122305 q = 1) (hb : d150351 q = 1) : d159559 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d150351, d159559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d150351, d159559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro31275 (p : Pattern) (ha : d122305 p = 1) (hb : d150354 p = 1) : d159562 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122305 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12463 q = 1) (hb : d122305 q = 1) : d158727 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d12463, d158727, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30846 q ha hb
    | true =>
      simp only [d12463, d158727, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30847 q ha hb
  have h2 (q : Pattern) (ha : d12464 q = 1) (hb : d122305 q = 1) : d158728 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d12464, d158728, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12464, d158728, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d12465 q = 1) (hb : d122305 q = 1) : d158729 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d12465, d158729, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d12465, d158729, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d12466 q = 1) (hb : d122305 q = 1) : d158730 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d12466, d158730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12466, d158730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d12467 q = 1) (hb : d122305 q = 1) : d158731 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d12467, d158731, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12467, d158731, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d122305 q = 1) (hb : d150354 q = 1) : d159562 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d150354, d159562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d150354, d159562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  exact h6 p ha hb
theorem andIntro31276 (p : Pattern) (ha : d122305 p = 1) (hb : d150365 p = 1) : d159573 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122305 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d122305 q = 1) (hb : d150360 q = 1) : d159568 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d150360, d159568, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30878 q hb ha
    | true =>
      simp only [d150360, d159568, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30853 q hb ha
  have h2 (q : Pattern) (ha : d122305 q = 1) (hb : d150361 q = 1) : d159569 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d150361, d159569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d150361, d159569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d122305 q = 1) (hb : d150362 q = 1) : d159570 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d150362, d159570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d150362, d159570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d122305 q = 1) (hb : d150363 q = 1) : d159571 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d150363, d159571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d150363, d159571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d122305 q = 1) (hb : d150364 q = 1) : d159572 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d150364, d159572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d150364, d159572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d122305 q = 1) (hb : d150365 q = 1) : d159573 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d150365, d159573, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d150365, d159573, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro31277 (p : Pattern) (ha : d122305 p = 1) (hb : d150371 p = 1) : d159579 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122305 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12469 q = 1) (hb : d122305 q = 1) : d158733 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d12469, d158733, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30845 q ha hb
    | true =>
      simp only [d12469, d158733, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30848 q ha hb
  have h2 (q : Pattern) (ha : d12470 q = 1) (hb : d122305 q = 1) : d158734 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d12470, d158734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d12470, d158734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d122305 q = 1) (hb : d150352 q = 1) : d159560 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d150352, d159560, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d150352, d159560, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d122305 q = 1) (hb : d150353 q = 1) : d159561 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d150353, d159561, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d150353, d159561, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d122305 q = 1) (hb : d150355 q = 1) : d159563 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d150355, d159563, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d150355, d159563, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31275 q ha hb
  have h6 (q : Pattern) (ha : d122305 q = 1) (hb : d150356 q = 1) : d159564 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d150356, d159564, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d150356, d159564, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d122305 q = 1) (hb : d150357 q = 1) : d159565 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d150357, d159565, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d150357, d159565, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d122305 q = 1) (hb : d150358 q = 1) : d159566 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d150358, d159566, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d150358, d159566, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d122305 q = 1) (hb : d150359 q = 1) : d159567 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d150359, d159567, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d150359, d159567, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d122305 q = 1) (hb : d150366 q = 1) : d159574 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d150366, d159574, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d150366, d159574, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31276 q ha hb
  have h11 (q : Pattern) (ha : d122305 q = 1) (hb : d150367 q = 1) : d159575 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d150367, d159575, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d150367, d159575, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d122305 q = 1) (hb : d150368 q = 1) : d159576 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d150368, d159576, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d150368, d159576, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d122305 q = 1) (hb : d150369 q = 1) : d159577 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d150369, d159577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d150369, d159577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h14 (q : Pattern) (ha : d122305 q = 1) (hb : d150370 q = 1) : d159578 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d150370, d159578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d150370, d159578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h15 (q : Pattern) (ha : d122305 q = 1) (hb : d150371 q = 1) : d159579 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d150371, d159579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d150371, d159579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro31278 (p : Pattern) (ha : d122305 p = 1) (hb : d150377 p = 1) : d159585 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122305 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d122305 q = 1) (hb : d150372 q = 1) : d159580 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d150372, d159580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d150372, d159580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31277 q ha hb
  have h2 (q : Pattern) (ha : d122305 q = 1) (hb : d150373 q = 1) : d159581 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d150373, d159581, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d150373, d159581, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d122305 q = 1) (hb : d150374 q = 1) : d159582 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d150374, d159582, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d150374, d159582, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d122305 q = 1) (hb : d150375 q = 1) : d159583 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d150375, d159583, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d150375, d159583, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d122305 q = 1) (hb : d150376 q = 1) : d159584 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d150376, d159584, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d150376, d159584, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d122305 q = 1) (hb : d150377 q = 1) : d159585 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d150377, d159585, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d150377, d159585, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro31279 (p : Pattern) (ha : d122305 p = 1) (hb : d150381 p = 1) : d159589 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122305 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12718 q = 1) (hb : d122305 q = 1) : d158870 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d12718, d158870, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30888 q ha hb
    | true =>
      simp only [d12718, d158870, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30889 q ha hb
  have h2 (q : Pattern) (ha : d12719 q = 1) (hb : d122305 q = 1) : d158871 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d12719, d158871, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12719, d158871, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d12720 q = 1) (hb : d122305 q = 1) : d158872 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d12720, d158872, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d12720, d158872, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d12721 q = 1) (hb : d122305 q = 1) : d158873 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d12721, d158873, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12721, d158873, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d12722 q = 1) (hb : d122305 q = 1) : d158874 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d12722, d158874, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12722, d158874, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d122305 q = 1) (hb : d150381 q = 1) : d159589 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d150381, d159589, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d150381, d159589, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  exact h6 p ha hb
theorem andIntro31280 (p : Pattern) (ha : d122305 p = 1) (hb : d150392 p = 1) : d159600 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122305 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d122305 q = 1) (hb : d150387 q = 1) : d159595 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d150387, d159595, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30920 q hb ha
    | true =>
      simp only [d150387, d159595, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30895 q hb ha
  have h2 (q : Pattern) (ha : d122305 q = 1) (hb : d150388 q = 1) : d159596 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d150388, d159596, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d150388, d159596, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d122305 q = 1) (hb : d150389 q = 1) : d159597 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d150389, d159597, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d150389, d159597, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d122305 q = 1) (hb : d150390 q = 1) : d159598 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d150390, d159598, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d150390, d159598, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d122305 q = 1) (hb : d150391 q = 1) : d159599 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d150391, d159599, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d150391, d159599, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d122305 q = 1) (hb : d150392 q = 1) : d159600 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d150392, d159600, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d150392, d159600, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro31281 (p : Pattern) (ha : d122305 p = 1) (hb : d150398 p = 1) : d159606 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122305 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12724 q = 1) (hb : d122305 q = 1) : d158876 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d12724, d158876, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30887 q ha hb
    | true =>
      simp only [d12724, d158876, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30890 q ha hb
  have h2 (q : Pattern) (ha : d12725 q = 1) (hb : d122305 q = 1) : d158877 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d12725, d158877, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d12725, d158877, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d122305 q = 1) (hb : d150379 q = 1) : d159587 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d150379, d159587, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d150379, d159587, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d122305 q = 1) (hb : d150380 q = 1) : d159588 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d150380, d159588, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d150380, d159588, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d122305 q = 1) (hb : d150382 q = 1) : d159590 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d150382, d159590, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d150382, d159590, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31279 q ha hb
  have h6 (q : Pattern) (ha : d122305 q = 1) (hb : d150383 q = 1) : d159591 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d150383, d159591, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d150383, d159591, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d122305 q = 1) (hb : d150384 q = 1) : d159592 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d150384, d159592, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d150384, d159592, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d122305 q = 1) (hb : d150385 q = 1) : d159593 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d150385, d159593, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d150385, d159593, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d122305 q = 1) (hb : d150386 q = 1) : d159594 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d150386, d159594, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d150386, d159594, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d122305 q = 1) (hb : d150393 q = 1) : d159601 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d150393, d159601, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d150393, d159601, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31280 q ha hb
  have h11 (q : Pattern) (ha : d122305 q = 1) (hb : d150394 q = 1) : d159602 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d150394, d159602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d150394, d159602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d122305 q = 1) (hb : d150395 q = 1) : d159603 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d150395, d159603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d150395, d159603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d122305 q = 1) (hb : d150396 q = 1) : d159604 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d150396, d159604, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d150396, d159604, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h14 (q : Pattern) (ha : d122305 q = 1) (hb : d150397 q = 1) : d159605 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d150397, d159605, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d150397, d159605, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h15 (q : Pattern) (ha : d122305 q = 1) (hb : d150398 q = 1) : d159606 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d150398, d159606, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d150398, d159606, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro31282 (p : Pattern) (ha : d122305 p = 1) (hb : d150404 p = 1) : d159612 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122305 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d122305 q = 1) (hb : d150399 q = 1) : d159607 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d150399, d159607, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d150399, d159607, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31281 q ha hb
  have h2 (q : Pattern) (ha : d122305 q = 1) (hb : d150400 q = 1) : d159608 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d150400, d159608, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d150400, d159608, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d122305 q = 1) (hb : d150401 q = 1) : d159609 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d150401, d159609, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d150401, d159609, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d122305 q = 1) (hb : d150402 q = 1) : d159610 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d150402, d159610, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d150402, d159610, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d122305 q = 1) (hb : d150403 q = 1) : d159611 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d150403, d159611, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d150403, d159611, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d122305 q = 1) (hb : d150404 q = 1) : d159612 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d150404, d159612, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d150404, d159612, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro31283 (p : Pattern) (ha : d122305 p = 1) (hb : d150409 p = 1) : d159617 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122305 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12992 q = 1) (hb : d122305 q = 1) : d159015 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d12992, d159015, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30931 q ha hb
    | true =>
      simp only [d12992, d159015, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30932 q ha hb
  have h2 (q : Pattern) (ha : d12993 q = 1) (hb : d122305 q = 1) : d159016 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d12993, d159016, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12993, d159016, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d12994 q = 1) (hb : d122305 q = 1) : d159017 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d12994, d159017, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d12994, d159017, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d12995 q = 1) (hb : d122305 q = 1) : d159018 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d12995, d159018, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12995, d159018, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d12996 q = 1) (hb : d122305 q = 1) : d159019 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d12996, d159019, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12996, d159019, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d122305 q = 1) (hb : d150409 q = 1) : d159617 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d150409, d159617, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d150409, d159617, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  exact h6 p ha hb
theorem andIntro31284 (p : Pattern) (ha : d122305 p = 1) (hb : d150418 p = 1) : d159626 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122305 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d13244 q = 1) (hb : d122305 q = 1) : d159134 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d13244, d159134, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30968 q ha hb
    | true =>
      simp only [d13244, d159134, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d13245 q = 1) (hb : d122305 q = 1) : d159135 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d13245, d159135, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13245, d159135, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d13197 q = 1) (hb : d122305 q = 1) : d124628 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d13197, d124628, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30939 q ha hb
    | true =>
      simp only [d13197, d124628, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d13198 q = 1) (hb : d122305 q = 1) : d124629 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d13198, d124629, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13198, d124629, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d122305 q = 1) (hb : d150415 q = 1) : d159623 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d150415, d159623, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d150415, d159623, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d122305 q = 1) (hb : d150416 q = 1) : d159624 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d150416, d159624, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d150416, d159624, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d122305 q = 1) (hb : d150417 q = 1) : d159625 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d150417, d159625, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d150417, d159625, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d122305 q = 1) (hb : d150418 q = 1) : d159626 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d150418, d159626, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d150418, d159626, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro31285 (p : Pattern) (ha : d122305 p = 1) (hb : d150424 p = 1) : d159632 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122305 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d122305 q = 1) (hb : d150419 q = 1) : d159627 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d150419, d159627, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31284 q ha hb
    | true =>
      simp only [d150419, d159627, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30940 q hb ha
  have h2 (q : Pattern) (ha : d122305 q = 1) (hb : d150420 q = 1) : d159628 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d150420, d159628, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d150420, d159628, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d122305 q = 1) (hb : d150421 q = 1) : d159629 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d150421, d159629, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d150421, d159629, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d122305 q = 1) (hb : d150422 q = 1) : d159630 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d150422, d159630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d150422, d159630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d122305 q = 1) (hb : d150423 q = 1) : d159631 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d150423, d159631, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d150423, d159631, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d122305 q = 1) (hb : d150424 q = 1) : d159632 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d150424, d159632, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d150424, d159632, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro31286 (p : Pattern) (ha : d122305 p = 1) (hb : d150430 p = 1) : d159638 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122305 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12998 q = 1) (hb : d122305 q = 1) : d159021 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d12998, d159021, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30930 q ha hb
    | true =>
      simp only [d12998, d159021, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30933 q ha hb
  have h2 (q : Pattern) (ha : d12999 q = 1) (hb : d122305 q = 1) : d159022 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d12999, d159022, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d12999, d159022, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d122305 q = 1) (hb : d150407 q = 1) : d159615 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d150407, d159615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d150407, d159615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d122305 q = 1) (hb : d150408 q = 1) : d159616 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d150408, d159616, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d150408, d159616, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d122305 q = 1) (hb : d150410 q = 1) : d159618 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d150410, d159618, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d150410, d159618, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31283 q ha hb
  have h6 (q : Pattern) (ha : d122305 q = 1) (hb : d150411 q = 1) : d159619 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d150411, d159619, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d150411, d159619, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d122305 q = 1) (hb : d150412 q = 1) : d159620 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d150412, d159620, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d150412, d159620, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d122305 q = 1) (hb : d150413 q = 1) : d159621 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d150413, d159621, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d150413, d159621, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d122305 q = 1) (hb : d150414 q = 1) : d159622 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d150414, d159622, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d150414, d159622, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d122305 q = 1) (hb : d150425 q = 1) : d159633 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d150425, d159633, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d150425, d159633, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31285 q ha hb
  have h11 (q : Pattern) (ha : d122305 q = 1) (hb : d150426 q = 1) : d159634 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d150426, d159634, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d150426, d159634, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d122305 q = 1) (hb : d150427 q = 1) : d159635 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d150427, d159635, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d150427, d159635, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d122305 q = 1) (hb : d150428 q = 1) : d159636 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d150428, d159636, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d150428, d159636, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h14 (q : Pattern) (ha : d122305 q = 1) (hb : d150429 q = 1) : d159637 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d150429, d159637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d150429, d159637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h15 (q : Pattern) (ha : d122305 q = 1) (hb : d150430 q = 1) : d159638 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d150430, d159638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d150430, d159638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro31287 (p : Pattern) (ha : d122305 p = 1) (hb : d150436 p = 1) : d159644 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122305 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d122305 q = 1) (hb : d150431 q = 1) : d159639 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d150431, d159639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d150431, d159639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31286 q ha hb
  have h2 (q : Pattern) (ha : d122305 q = 1) (hb : d150432 q = 1) : d159640 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d150432, d159640, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d150432, d159640, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d122305 q = 1) (hb : d150433 q = 1) : d159641 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d150433, d159641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d150433, d159641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d122305 q = 1) (hb : d150434 q = 1) : d159642 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d150434, d159642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d150434, d159642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d122305 q = 1) (hb : d150435 q = 1) : d159643 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d150435, d159643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d150435, d159643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d122305 q = 1) (hb : d150436 q = 1) : d159644 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d150436, d159644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d150436, d159644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro31288 (p : Pattern) (ha : d122305 p = 1) (hb : d150442 p = 1) : d159650 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122305 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d13318 q = 1) (hb : d122305 q = 1) : d159179 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d13318, d159179, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30979 q ha hb
    | true =>
      simp only [d13318, d159179, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30980 q ha hb
  have h2 (q : Pattern) (ha : d13319 q = 1) (hb : d122305 q = 1) : d159180 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d13319, d159180, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13319, d159180, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d13320 q = 1) (hb : d122305 q = 1) : d159181 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d13320, d159181, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d13320, d159181, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d13321 q = 1) (hb : d122305 q = 1) : d159182 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d13321, d159182, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13321, d159182, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d13322 q = 1) (hb : d122305 q = 1) : d159183 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d13322, d159183, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13322, d159183, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d122305 q = 1) (hb : d150442 q = 1) : d159650 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d150442, d159650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d150442, d159650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  exact h6 p ha hb
theorem andIntro31289 (p : Pattern) (ha : d122305 p = 1) (hb : d150451 p = 1) : d159659 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122305 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d13570 q = 1) (hb : d122305 q = 1) : d159298 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d13570, d159298, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31016 q ha hb
    | true =>
      simp only [d13570, d159298, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d13571 q = 1) (hb : d122305 q = 1) : d159299 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d13571, d159299, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13571, d159299, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d13523 q = 1) (hb : d122305 q = 1) : d124862 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d13523, d124862, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30987 q ha hb
    | true =>
      simp only [d13523, d124862, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d13524 q = 1) (hb : d122305 q = 1) : d124863 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d13524, d124863, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13524, d124863, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d122305 q = 1) (hb : d150448 q = 1) : d159656 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d150448, d159656, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d150448, d159656, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d122305 q = 1) (hb : d150449 q = 1) : d159657 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d150449, d159657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d150449, d159657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d122305 q = 1) (hb : d150450 q = 1) : d159658 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d150450, d159658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d150450, d159658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d122305 q = 1) (hb : d150451 q = 1) : d159659 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d150451, d159659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d150451, d159659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro31290 (p : Pattern) (ha : d122305 p = 1) (hb : d150457 p = 1) : d159665 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122305 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d122305 q = 1) (hb : d150452 q = 1) : d159660 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d150452, d159660, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31289 q ha hb
    | true =>
      simp only [d150452, d159660, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30988 q hb ha
  have h2 (q : Pattern) (ha : d122305 q = 1) (hb : d150453 q = 1) : d159661 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d150453, d159661, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d150453, d159661, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d122305 q = 1) (hb : d150454 q = 1) : d159662 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d150454, d159662, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d150454, d159662, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d122305 q = 1) (hb : d150455 q = 1) : d159663 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d150455, d159663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d150455, d159663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d122305 q = 1) (hb : d150456 q = 1) : d159664 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d150456, d159664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d150456, d159664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d122305 q = 1) (hb : d150457 q = 1) : d159665 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d150457, d159665, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d150457, d159665, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro31291 (p : Pattern) (ha : d122305 p = 1) (hb : d150463 p = 1) : d159671 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122305 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d13324 q = 1) (hb : d122305 q = 1) : d159185 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d13324, d159185, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30978 q ha hb
    | true =>
      simp only [d13324, d159185, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30981 q ha hb
  have h2 (q : Pattern) (ha : d13325 q = 1) (hb : d122305 q = 1) : d159186 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d13325, d159186, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d13325, d159186, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d122305 q = 1) (hb : d150440 q = 1) : d159648 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d150440, d159648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d150440, d159648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d122305 q = 1) (hb : d150441 q = 1) : d159649 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d150441, d159649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d150441, d159649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d122305 q = 1) (hb : d150443 q = 1) : d159651 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d150443, d159651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d150443, d159651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31288 q ha hb
  have h6 (q : Pattern) (ha : d122305 q = 1) (hb : d150444 q = 1) : d159652 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d150444, d159652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d150444, d159652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d122305 q = 1) (hb : d150445 q = 1) : d159653 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d150445, d159653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d150445, d159653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d122305 q = 1) (hb : d150446 q = 1) : d159654 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d150446, d159654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d150446, d159654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d122305 q = 1) (hb : d150447 q = 1) : d159655 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d150447, d159655, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d150447, d159655, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d122305 q = 1) (hb : d150458 q = 1) : d159666 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d150458, d159666, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d150458, d159666, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31290 q ha hb
  have h11 (q : Pattern) (ha : d122305 q = 1) (hb : d150459 q = 1) : d159667 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d150459, d159667, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d150459, d159667, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d122305 q = 1) (hb : d150460 q = 1) : d159668 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d150460, d159668, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d150460, d159668, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d122305 q = 1) (hb : d150461 q = 1) : d159669 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d150461, d159669, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d150461, d159669, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h14 (q : Pattern) (ha : d122305 q = 1) (hb : d150462 q = 1) : d159670 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d150462, d159670, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d150462, d159670, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h15 (q : Pattern) (ha : d122305 q = 1) (hb : d150463 q = 1) : d159671 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d150463, d159671, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d150463, d159671, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro31292 (p : Pattern) (ha : d122305 p = 1) (hb : d150469 p = 1) : d159677 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122305 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d122305 q = 1) (hb : d150464 q = 1) : d159672 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d150464, d159672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d150464, d159672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31291 q ha hb
  have h2 (q : Pattern) (ha : d122305 q = 1) (hb : d150465 q = 1) : d159673 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d150465, d159673, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d150465, d159673, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d122305 q = 1) (hb : d150466 q = 1) : d159674 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d150466, d159674, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d150466, d159674, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d122305 q = 1) (hb : d150467 q = 1) : d159675 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d150467, d159675, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d150467, d159675, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d122305 q = 1) (hb : d150468 q = 1) : d159676 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d150468, d159676, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d150468, d159676, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d122305 q = 1) (hb : d150469 q = 1) : d159677 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d150469, d159677, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d150469, d159677, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro31293 (p : Pattern) (ha : d122305 p = 1) (hb : d150476 p = 1) : d159684 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122305 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d13645 q = 1) (hb : d122305 q = 1) : d159344 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d13645, d159344, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31027 q ha hb
    | true =>
      simp only [d13645, d159344, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31028 q ha hb
  have h2 (q : Pattern) (ha : d13646 q = 1) (hb : d122305 q = 1) : d159345 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d13646, d159345, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13646, d159345, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d13647 q = 1) (hb : d122305 q = 1) : d159346 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d13647, d159346, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d13647, d159346, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d13648 q = 1) (hb : d122305 q = 1) : d159347 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d13648, d159347, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13648, d159347, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d13649 q = 1) (hb : d122305 q = 1) : d159348 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d13649, d159348, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13649, d159348, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d122305 q = 1) (hb : d150476 q = 1) : d159684 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d150476, d159684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d150476, d159684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  exact h6 p ha hb
theorem andIntro31294 (p : Pattern) (ha : d122305 p = 1) (hb : d150485 p = 1) : d159693 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122305 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d13897 q = 1) (hb : d122305 q = 1) : d159463 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d13897, d159463, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31064 q ha hb
    | true =>
      simp only [d13897, d159463, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d13898 q = 1) (hb : d122305 q = 1) : d159464 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d13898, d159464, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13898, d159464, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d13850 q = 1) (hb : d122305 q = 1) : d125095 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d13850, d125095, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31035 q ha hb
    | true =>
      simp only [d13850, d125095, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d13851 q = 1) (hb : d122305 q = 1) : d125096 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d13851, d125096, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13851, d125096, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d122305 q = 1) (hb : d150482 q = 1) : d159690 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d150482, d159690, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d150482, d159690, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d122305 q = 1) (hb : d150483 q = 1) : d159691 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d150483, d159691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d150483, d159691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d122305 q = 1) (hb : d150484 q = 1) : d159692 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d150484, d159692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d150484, d159692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d122305 q = 1) (hb : d150485 q = 1) : d159693 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d150485, d159693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d150485, d159693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro31295 (p : Pattern) (ha : d122305 p = 1) (hb : d150491 p = 1) : d159699 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122305 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d122305 q = 1) (hb : d150486 q = 1) : d159694 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d150486, d159694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31294 q ha hb
    | true =>
      simp only [d150486, d159694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31036 q hb ha
  have h2 (q : Pattern) (ha : d122305 q = 1) (hb : d150487 q = 1) : d159695 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d150487, d159695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d150487, d159695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d122305 q = 1) (hb : d150488 q = 1) : d159696 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d150488, d159696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d150488, d159696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d122305 q = 1) (hb : d150489 q = 1) : d159697 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d150489, d159697, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d150489, d159697, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d122305 q = 1) (hb : d150490 q = 1) : d159698 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d150490, d159698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d150490, d159698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d122305 q = 1) (hb : d150491 q = 1) : d159699 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d150491, d159699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d150491, d159699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro31296 (p : Pattern) (ha : d122305 p = 1) (hb : d150497 p = 1) : d159705 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122305 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d13651 q = 1) (hb : d122305 q = 1) : d159350 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d13651, d159350, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31026 q ha hb
    | true =>
      simp only [d13651, d159350, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31029 q ha hb
  have h2 (q : Pattern) (ha : d13652 q = 1) (hb : d122305 q = 1) : d159351 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d13652, d159351, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d13652, d159351, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d122305 q = 1) (hb : d150474 q = 1) : d159682 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d150474, d159682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d150474, d159682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d122305 q = 1) (hb : d150475 q = 1) : d159683 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d150475, d159683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d150475, d159683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d122305 q = 1) (hb : d150477 q = 1) : d159685 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d150477, d159685, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d150477, d159685, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31293 q ha hb
  have h6 (q : Pattern) (ha : d122305 q = 1) (hb : d150478 q = 1) : d159686 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d150478, d159686, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d150478, d159686, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d122305 q = 1) (hb : d150479 q = 1) : d159687 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d150479, d159687, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d150479, d159687, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d122305 q = 1) (hb : d150480 q = 1) : d159688 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d150480, d159688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d150480, d159688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d122305 q = 1) (hb : d150481 q = 1) : d159689 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d150481, d159689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d150481, d159689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d122305 q = 1) (hb : d150492 q = 1) : d159700 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d150492, d159700, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d150492, d159700, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31295 q ha hb
  have h11 (q : Pattern) (ha : d122305 q = 1) (hb : d150493 q = 1) : d159701 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d150493, d159701, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d150493, d159701, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d122305 q = 1) (hb : d150494 q = 1) : d159702 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d150494, d159702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d150494, d159702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d122305 q = 1) (hb : d150495 q = 1) : d159703 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d150495, d159703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d150495, d159703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h14 (q : Pattern) (ha : d122305 q = 1) (hb : d150496 q = 1) : d159704 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d150496, d159704, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d150496, d159704, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h15 (q : Pattern) (ha : d122305 q = 1) (hb : d150497 q = 1) : d159705 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d150497, d159705, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d150497, d159705, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro31297 (p : Pattern) (ha : d122305 p = 1) (hb : d150503 p = 1) : d159711 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122305 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d122305 q = 1) (hb : d150498 q = 1) : d159706 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d150498, d159706, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d150498, d159706, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31296 q ha hb
  have h2 (q : Pattern) (ha : d122305 q = 1) (hb : d150499 q = 1) : d159707 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d150499, d159707, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d150499, d159707, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d122305 q = 1) (hb : d150500 q = 1) : d159708 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d150500, d159708, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d150500, d159708, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d122305 q = 1) (hb : d150501 q = 1) : d159709 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d150501, d159709, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d150501, d159709, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d122305 q = 1) (hb : d150502 q = 1) : d159710 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d150502, d159710, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d150502, d159710, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d122305 q = 1) (hb : d150503 q = 1) : d159711 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d150503, d159711, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d150503, d159711, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro31298 (p : Pattern) (ha : d122305 p = 1) (hb : d150509 p = 1) : d159717 p = 1 := by
  have h0 (q : Pattern) (ha : d122305 q = 1) (hb : d150378 q = 1) : d159586 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d150378, d159586, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31274 q ha hb
    | true =>
      simp only [d150378, d159586, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31278 q ha hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d122305 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d122305 q = 1) (hb : d150405 q = 1) : d159613 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d150405, d159613, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d150405, d159613, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31282 q ha hb
  have h3 (q : Pattern) (ha : d122305 q = 1) (hb : d150406 q = 1) : d159614 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d150406, d159614, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d150406, d159614, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d122305 q = 1) (hb : d150437 q = 1) : d159645 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d150437, d159645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d150437, d159645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31287 q ha hb
  have h5 (q : Pattern) (ha : d122305 q = 1) (hb : d150438 q = 1) : d159646 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d150438, d159646, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d150438, d159646, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d122305 q = 1) (hb : d150439 q = 1) : d159647 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d150439, d159647, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d150439, d159647, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d122305 q = 1) (hb : d150470 q = 1) : d159678 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d150470, d159678, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d150470, d159678, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31292 q ha hb
  have h8 (q : Pattern) (ha : d122305 q = 1) (hb : d150471 q = 1) : d159679 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d150471, d159679, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d150471, d159679, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d122305 q = 1) (hb : d150472 q = 1) : d159680 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d150472, d159680, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d150472, d159680, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d122305 q = 1) (hb : d150473 q = 1) : d159681 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d150473, d159681, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d150473, d159681, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d122305 q = 1) (hb : d150504 q = 1) : d159712 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d150504, d159712, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d150504, d159712, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31297 q ha hb
  have h12 (q : Pattern) (ha : d122305 q = 1) (hb : d150505 q = 1) : d159713 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d150505, d159713, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d150505, d159713, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d122305 q = 1) (hb : d150506 q = 1) : d159714 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d150506, d159714, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d150506, d159714, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d122305 q = 1) (hb : d150507 q = 1) : d159715 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d150507, d159715, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d150507, d159715, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d122305 q = 1) (hb : d150508 q = 1) : d159716 q = 1 := by
    cases bit : q 10250 with
    | false =>
      simp only [d150508, d159716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d150508, d159716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d122305 q = 1) (hb : d150509 q = 1) : d159717 q = 1 := by
    cases bit : q 260 with
    | false =>
      simp only [d150509, d159717, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d150509, d159717, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  exact h16 p ha hb
theorem andIntro31299 (p : Pattern) (ha : d122305 p = 1) (hb : d150515 p = 1) : d159723 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122305 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d122305 q = 1) (hb : d150510 q = 1) : d159718 q = 1 := by
    cases bit : q 259 with
    | false =>
      simp only [d150510, d159718, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31298 q ha hb
    | true =>
      simp only [d150510, d159718, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d122305 q = 1) (hb : d150511 q = 1) : d159719 q = 1 := by
    cases bit : q 258 with
    | false =>
      simp only [d150511, d159719, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d150511, d159719, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d122305 q = 1) (hb : d150512 q = 1) : d159720 q = 1 := by
    cases bit : q 257 with
    | false =>
      simp only [d150512, d159720, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d150512, d159720, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d122305 q = 1) (hb : d150513 q = 1) : d159721 q = 1 := by
    cases bit : q 256 with
    | false =>
      simp only [d150513, d159721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d150513, d159721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d122305 q = 1) (hb : d150514 q = 1) : d159722 q = 1 := by
    cases bit : q 255 with
    | false =>
      simp only [d150514, d159722, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d150514, d159722, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d122305 q = 1) (hb : d150515 q = 1) : d159723 q = 1 := by
    cases bit : q 254 with
    | false =>
      simp only [d150515, d159723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d150515, d159723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro31300 (p : Pattern) (ha : d122305 p = 1) (hb : d150521 p = 1) : d159729 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122305 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d122305 q = 1) (hb : d150516 q = 1) : d159724 q = 1 := by
    cases bit : q 253 with
    | false =>
      simp only [d150516, d159724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31299 q ha hb
    | true =>
      simp only [d150516, d159724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d122305 q = 1) (hb : d150517 q = 1) : d159725 q = 1 := by
    cases bit : q 252 with
    | false =>
      simp only [d150517, d159725, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d150517, d159725, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d122305 q = 1) (hb : d150518 q = 1) : d159726 q = 1 := by
    cases bit : q 251 with
    | false =>
      simp only [d150518, d159726, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d150518, d159726, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d122305 q = 1) (hb : d150519 q = 1) : d159727 q = 1 := by
    cases bit : q 250 with
    | false =>
      simp only [d150519, d159727, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d150519, d159727, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d122305 q = 1) (hb : d150520 q = 1) : d159728 q = 1 := by
    cases bit : q 249 with
    | false =>
      simp only [d150520, d159728, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d150520, d159728, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d122305 q = 1) (hb : d150521 q = 1) : d159729 q = 1 := by
    cases bit : q 245 with
    | false =>
      simp only [d150521, d159729, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d150521, d159729, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro31301 (p : Pattern) (ha : d122305 p = 1) (hb : d150527 p = 1) : d159735 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122305 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d122305 q = 1) (hb : d150522 q = 1) : d159730 q = 1 := by
    cases bit : q 200 with
    | false =>
      simp only [d150522, d159730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31300 q ha hb
    | true =>
      simp only [d150522, d159730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d122305 q = 1) (hb : d150523 q = 1) : d159731 q = 1 := by
    cases bit : q 199 with
    | false =>
      simp only [d150523, d159731, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d150523, d159731, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d122305 q = 1) (hb : d150524 q = 1) : d159732 q = 1 := by
    cases bit : q 186 with
    | false =>
      simp only [d150524, d159732, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d150524, d159732, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d122305 q = 1) (hb : d150525 q = 1) : d159733 q = 1 := by
    cases bit : q 185 with
    | false =>
      simp only [d150525, d159733, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d150525, d159733, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d122305 q = 1) (hb : d150526 q = 1) : d159734 q = 1 := by
    cases bit : q 184 with
    | false =>
      simp only [d150526, d159734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d150526, d159734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d122305 q = 1) (hb : d150527 q = 1) : d159735 q = 1 := by
    cases bit : q 181 with
    | false =>
      simp only [d150527, d159735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d150527, d159735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro31302 (p : Pattern) (ha : d122305 p = 1) (hb : d150533 p = 1) : d159741 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122305 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d122305 q = 1) (hb : d150528 q = 1) : d159736 q = 1 := by
    cases bit : q 177 with
    | false =>
      simp only [d150528, d159736, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31301 q ha hb
    | true =>
      simp only [d150528, d159736, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d122305 q = 1) (hb : d150529 q = 1) : d159737 q = 1 := by
    cases bit : q 164 with
    | false =>
      simp only [d150529, d159737, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d150529, d159737, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d122305 q = 1) (hb : d150530 q = 1) : d159738 q = 1 := by
    cases bit : q 156 with
    | false =>
      simp only [d150530, d159738, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d150530, d159738, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d122305 q = 1) (hb : d150531 q = 1) : d159739 q = 1 := by
    cases bit : q 155 with
    | false =>
      simp only [d150531, d159739, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d150531, d159739, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d122305 q = 1) (hb : d150532 q = 1) : d159740 q = 1 := by
    cases bit : q 134 with
    | false =>
      simp only [d150532, d159740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d150532, d159740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d122305 q = 1) (hb : d150533 q = 1) : d159741 q = 1 := by
    cases bit : q 133 with
    | false =>
      simp only [d150533, d159741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d150533, d159741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro31303 (p : Pattern) (ha : d122305 p = 1) (hb : d150539 p = 1) : d159747 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122305 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d122305 q = 1) (hb : d150534 q = 1) : d159742 q = 1 := by
    cases bit : q 120 with
    | false =>
      simp only [d150534, d159742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31302 q ha hb
    | true =>
      simp only [d150534, d159742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d122305 q = 1) (hb : d150535 q = 1) : d159743 q = 1 := by
    cases bit : q 118 with
    | false =>
      simp only [d150535, d159743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d150535, d159743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d122305 q = 1) (hb : d150536 q = 1) : d159744 q = 1 := by
    cases bit : q 114 with
    | false =>
      simp only [d150536, d159744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d150536, d159744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d122305 q = 1) (hb : d150537 q = 1) : d159745 q = 1 := by
    cases bit : q 111 with
    | false =>
      simp only [d150537, d159745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d150537, d159745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d122305 q = 1) (hb : d150538 q = 1) : d159746 q = 1 := by
    cases bit : q 98 with
    | false =>
      simp only [d150538, d159746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d150538, d159746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d122305 q = 1) (hb : d150539 q = 1) : d159747 q = 1 := by
    cases bit : q 97 with
    | false =>
      simp only [d150539, d159747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d150539, d159747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro31304 (p : Pattern) (ha : d122305 p = 1) (hb : d150545 p = 1) : d159753 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122305 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d122305 q = 1) (hb : d150540 q = 1) : d159748 q = 1 := by
    cases bit : q 94 with
    | false =>
      simp only [d150540, d159748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31303 q ha hb
    | true =>
      simp only [d150540, d159748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d122305 q = 1) (hb : d150541 q = 1) : d159749 q = 1 := by
    cases bit : q 76 with
    | false =>
      simp only [d150541, d159749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d150541, d159749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d122305 q = 1) (hb : d150542 q = 1) : d159750 q = 1 := by
    cases bit : q 67 with
    | false =>
      simp only [d150542, d159750, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d150542, d159750, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d122305 q = 1) (hb : d150543 q = 1) : d159751 q = 1 := by
    cases bit : q 52 with
    | false =>
      simp only [d150543, d159751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d150543, d159751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d122305 q = 1) (hb : d150544 q = 1) : d159752 q = 1 := by
    cases bit : q 47 with
    | false =>
      simp only [d150544, d159752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d150544, d159752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d122305 q = 1) (hb : d150545 q = 1) : d159753 q = 1 := by
    cases bit : q 46 with
    | false =>
      simp only [d150545, d159753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d150545, d159753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro31305 (p : Pattern) (ha : d122305 p = 1) (hb : d150551 p = 1) : d159759 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122305 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d122305 q = 1) (hb : d150546 q = 1) : d159754 q = 1 := by
    cases bit : q 45 with
    | false =>
      simp only [d150546, d159754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31304 q ha hb
    | true =>
      simp only [d150546, d159754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d122305 q = 1) (hb : d150547 q = 1) : d159755 q = 1 := by
    cases bit : q 30 with
    | false =>
      simp only [d150547, d159755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d150547, d159755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d122305 q = 1) (hb : d150548 q = 1) : d159756 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d150548, d159756, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d150548, d159756, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d122305 q = 1) (hb : d150549 q = 1) : d159757 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d150549, d159757, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d150549, d159757, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d122305 q = 1) (hb : d150550 q = 1) : d159758 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d150550, d159758, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d150550, d159758, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d122305 q = 1) (hb : d150551 q = 1) : d159759 q = 1 := by
    cases bit : q 25 with
    | false =>
      simp only [d150551, d159759, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d150551, d159759, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro31306 (p : Pattern) (ha : d122430 p = 1) (hb : d158600 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d122397 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d122403 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d122419 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d122321 q = 1) (hb : d158545 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d122321, d158545, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31078 q ha hb
    | true =>
      simp only [d122321, d158545, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5 q hb ha
  have h5 (q : Pattern) (ha : d122420 q = 1) (hb : d158596 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d122420, d158596, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d122420, d158596, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d122426 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d122427 q = 1) (hb : d158597 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d122427, d158597, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d122427, d158597, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d122428 q = 1) (hb : d158598 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d122428, d158598, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d122428, d158598, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d122429 q = 1) (hb : d158599 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d122429, d158599, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d122429, d158599, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d122430 q = 1) (hb : d158600 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d122430, d158600, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d122430, d158600, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro31307 (p : Pattern) (ha : d122449 p = 1) (hb : d158607 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122397 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d122403 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d122419 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d122321 q = 1) (hb : d158545 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d122321, d158545, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31078 q ha hb
    | true =>
      simp only [d122321, d158545, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5 q hb ha
  have h4 (q : Pattern) (ha : d122420 q = 1) (hb : d158596 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d122420, d158596, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d122420, d158596, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d122426 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d122427 q = 1) (hb : d158597 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d122427, d158597, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d122427, d158597, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d122428 q = 1) (hb : d158598 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d122428, d158598, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d122428, d158598, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d122429 q = 1) (hb : d158599 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d122429, d158599, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d122429, d158599, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d122435 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d122439 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d122441 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d122328 q = 1) (hb : d158552 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d122328, d158552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31080 q ha hb
    | true =>
      simp only [d122328, d158552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7 q hb ha
  have h13 (q : Pattern) (ha : d122442 q = 1) (hb : d158603 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d122442, d158603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
    | true =>
      simp only [d122442, d158603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d122445 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d122446 q = 1) (hb : d158604 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d122446, d158604, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d122446, d158604, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d122447 q = 1) (hb : d158605 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d122447, d158605, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
    | true =>
      simp only [d122447, d158605, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d122448 q = 1) (hb : d158606 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d122448, d158606, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
    | true =>
      simp only [d122448, d158606, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d122449 q = 1) (hb : d158607 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d122449, d158607, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d122449, d158607, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro31308 (p : Pattern) (ha : d122458 p = 1) (hb : d159537 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d122441 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d122328 q = 1) (hb : d158552 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d122328, d158552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31080 q ha hb
    | true =>
      simp only [d122328, d158552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7 q hb ha
  have h3 (q : Pattern) (ha : d122442 q = 1) (hb : d158603 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d122442, d158603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d122442, d158603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d122445 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d122446 q = 1) (hb : d158604 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d122446, d158604, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d122446, d158604, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d122456 q = 1) (hb : d158605 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d122456, d158605, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d122456, d158605, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d122457 q = 1) (hb : d158606 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d122457, d158606, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d122457, d158606, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d122458 q = 1) (hb : d159537 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d122458, d159537, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d122458, d159537, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro31309 (p : Pattern) (ha : d122490 p = 1) (hb : d159547 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d122479 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d122360 q = 1) (hb : d158579 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d122360, d158579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31084 q ha hb
    | true =>
      simp only [d122360, d158579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12 q hb ha
  have h3 (q : Pattern) (ha : d122480 q = 1) (hb : d159543 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d122480, d159543, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d122480, d159543, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d122486 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d122487 q = 1) (hb : d159544 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d122487, d159544, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d122487, d159544, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d122488 q = 1) (hb : d159545 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d122488, d159545, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d122488, d159545, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d122489 q = 1) (hb : d159546 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d122489, d159546, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d122489, d159546, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d122490 q = 1) (hb : d159547 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d122490, d159547, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d122490, d159547, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro31310 (p : Pattern) (ha : d122496 p = 1) (hb : d159553 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122391 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d122450 q = 1) (hb : d158608 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d122450, d158608, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31306 q ha hb
    | true =>
      simp only [d122450, d158608, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31307 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d122452 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d122453 q = 1) (hb : d158609 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d122453, d158609, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d122453, d158609, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d122454 q = 1) (hb : d159535 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d122454, d159535, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d122454, d159535, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d122455 q = 1) (hb : d159536 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d122455, d159536, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d122455, d159536, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d122459 q = 1) (hb : d159538 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d122459, d159538, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d122459, d159538, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31308 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d52173 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d122460 q = 1) (hb : d159539 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d122460, d159539, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d122460, d159539, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d122461 q = 1) (hb : d159540 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d122461, d159540, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d122461, d159540, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h11 (q : Pattern) (ha : d122462 q = 1) (hb : d159541 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d122462, d159541, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d122462, d159541, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h12 (q : Pattern) (ha : d122463 q = 1) (hb : d159542 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d122463, d159542, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d122463, d159542, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d122491 q = 1) (hb : d159548 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d122491, d159548, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d122491, d159548, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31309 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d52210 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d122492 q = 1) (hb : d159549 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d122492, d159549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d122492, d159549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d122493 q = 1) (hb : d159550 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d122493, d159550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d122493, d159550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h17 (q : Pattern) (ha : d122494 q = 1) (hb : d159551 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d122494, d159551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d122494, d159551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h18 (q : Pattern) (ha : d122495 q = 1) (hb : d159552 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d122495, d159552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d122495, d159552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h19 (q : Pattern) (ha : d122496 q = 1) (hb : d159553 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d122496, d159553, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d122496, d159553, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro31311 (p : Pattern) (ha : d122502 p = 1) (hb : d159559 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d51951 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d53648 q = 1) (hb : d122372 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d53648, d122372, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d53648, d122372, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22453 q ha hb
  have h3 (q : Pattern) (ha : d53649 q = 1) (hb : d122373 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d53649, d122373, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d53649, d122373, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d53650 q = 1) (hb : d122374 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d53650, d122374, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d53650, d122374, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d53651 q = 1) (hb : d122375 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d53651, d122375, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d53651, d122375, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d53652 q = 1) (hb : d122376 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d53652, d122376, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53652, d122376, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d122497 q = 1) (hb : d159554 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d122497, d159554, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d122497, d159554, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31310 q ha hb
  have h8 (q : Pattern) (ha : d122498 q = 1) (hb : d159555 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d122498, d159555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d122498, d159555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d122499 q = 1) (hb : d159556 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d122499, d159556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d122499, d159556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d122500 q = 1) (hb : d159557 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d122500, d159557, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d122500, d159557, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d122501 q = 1) (hb : d159558 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d122501, d159558, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d122501, d159558, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d122502 q = 1) (hb : d159559 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d122502, d159559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
    | true =>
      simp only [d122502, d159559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  exact h12 p ha hb
theorem andIntro31312 (p : Pattern) (ha : d122586 p = 1) (hb : d158723 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d122546 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d122555 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d122575 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d122520 q = 1) (hb : d158718 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d122520, d158718, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31109 q ha hb
    | true =>
      simp only [d122520, d158718, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22166 q ha hb
  have h5 (q : Pattern) (ha : d122576 q = 1) (hb : d158719 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d122576, d158719, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d122576, d158719, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d122582 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d122583 q = 1) (hb : d158720 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d122583, d158720, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d122583, d158720, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d122584 q = 1) (hb : d158721 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d122584, d158721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d122584, d158721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d122585 q = 1) (hb : d158722 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d122585, d158722, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d122585, d158722, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d122586 q = 1) (hb : d158723 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d122586, d158723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d122586, d158723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro31313 (p : Pattern) (ha : d122607 p = 1) (hb : d158732 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122546 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d122555 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d122575 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d122520 q = 1) (hb : d158718 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d122520, d158718, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31109 q ha hb
    | true =>
      simp only [d122520, d158718, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22166 q ha hb
  have h4 (q : Pattern) (ha : d122576 q = 1) (hb : d158719 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d122576, d158719, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d122576, d158719, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d122582 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d122583 q = 1) (hb : d158720 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d122583, d158720, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d122583, d158720, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d122584 q = 1) (hb : d158721 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d122584, d158721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d122584, d158721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d122585 q = 1) (hb : d158722 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d122585, d158722, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d122585, d158722, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d122592 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d122597 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d122599 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d122530 q = 1) (hb : d158727 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d122530, d158727, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31111 q ha hb
    | true =>
      simp only [d122530, d158727, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22169 q ha hb
  have h13 (q : Pattern) (ha : d122600 q = 1) (hb : d158728 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d122600, d158728, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
    | true =>
      simp only [d122600, d158728, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d122603 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d122604 q = 1) (hb : d158729 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d122604, d158729, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d122604, d158729, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d122605 q = 1) (hb : d158730 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d122605, d158730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
    | true =>
      simp only [d122605, d158730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d122606 q = 1) (hb : d158731 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d122606, d158731, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
    | true =>
      simp only [d122606, d158731, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d122607 q = 1) (hb : d158732 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d122607, d158732, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d122607, d158732, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro31314 (p : Pattern) (ha : d122627 p = 1) (hb : d159562 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d122599 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d122530 q = 1) (hb : d158727 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d122530, d158727, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31111 q ha hb
    | true =>
      simp only [d122530, d158727, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22169 q ha hb
  have h3 (q : Pattern) (ha : d122600 q = 1) (hb : d158728 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d122600, d158728, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d122600, d158728, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d122603 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d122604 q = 1) (hb : d158729 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d122604, d158729, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d122604, d158729, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d122625 q = 1) (hb : d158730 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d122625, d158730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d122625, d158730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d122626 q = 1) (hb : d158731 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d122626, d158731, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d122626, d158731, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d122627 q = 1) (hb : d159562 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d122627, d159562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d122627, d159562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro31315 (p : Pattern) (ha : d122683 p = 1) (hb : d159573 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d122667 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d122672 q = 1) (hb : d159568 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d122672, d159568, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31131 q ha hb
    | true =>
      simp only [d122672, d159568, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22199 q ha hb
  have h3 (q : Pattern) (ha : d122673 q = 1) (hb : d159569 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d122673, d159569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d122673, d159569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d122679 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d122680 q = 1) (hb : d159570 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d122680, d159570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d122680, d159570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d122681 q = 1) (hb : d159571 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d122681, d159571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d122681, d159571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d122682 q = 1) (hb : d159572 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d122682, d159572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d122682, d159572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d122683 q = 1) (hb : d159573 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d122683, d159573, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d122683, d159573, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro31316 (p : Pattern) (ha : d122696 p = 1) (hb : d159579 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122538 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d122608 q = 1) (hb : d158733 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d122608, d158733, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31312 q ha hb
    | true =>
      simp only [d122608, d158733, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31313 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d122621 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d122622 q = 1) (hb : d158734 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d122622, d158734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d122622, d158734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d122623 q = 1) (hb : d159560 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d122623, d159560, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d122623, d159560, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d122624 q = 1) (hb : d159561 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d122624, d159561, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d122624, d159561, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d122628 q = 1) (hb : d159563 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d122628, d159563, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d122628, d159563, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31314 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d122630 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d122631 q = 1) (hb : d159564 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d122631, d159564, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d122631, d159564, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d122632 q = 1) (hb : d159565 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d122632, d159565, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d122632, d159565, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h11 (q : Pattern) (ha : d122633 q = 1) (hb : d159566 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d122633, d159566, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d122633, d159566, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h12 (q : Pattern) (ha : d122634 q = 1) (hb : d159567 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d122634, d159567, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d122634, d159567, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d122684 q = 1) (hb : d159574 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d122684, d159574, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d122684, d159574, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31315 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d122691 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d122692 q = 1) (hb : d159575 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d122692, d159575, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d122692, d159575, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d122693 q = 1) (hb : d159576 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d122693, d159576, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d122693, d159576, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h17 (q : Pattern) (ha : d122694 q = 1) (hb : d159577 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d122694, d159577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d122694, d159577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h18 (q : Pattern) (ha : d122695 q = 1) (hb : d159578 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d122695, d159578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d122695, d159578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h19 (q : Pattern) (ha : d122696 q = 1) (hb : d159579 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d122696, d159579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d122696, d159579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro31317 (p : Pattern) (ha : d122702 p = 1) (hb : d159585 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d122697 q = 1) (hb : d159580 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d122697, d159580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d122697, d159580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31316 q ha hb
  have h2 (q : Pattern) (ha : d122698 q = 1) (hb : d159581 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d122698, d159581, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d122698, d159581, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d122699 q = 1) (hb : d159582 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d122699, d159582, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d122699, d159582, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d122700 q = 1) (hb : d159583 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d122700, d159583, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d122700, d159583, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d122701 q = 1) (hb : d159584 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d122701, d159584, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d122701, d159584, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d122702 q = 1) (hb : d159585 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d122702, d159585, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d122702, d159585, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro31318 (p : Pattern) (ha : d122797 p = 1) (hb : d158866 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d122755 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d122764 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d122786 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d122729 q = 1) (hb : d158861 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d122729, d158861, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31137 q ha hb
    | true =>
      simp only [d122729, d158861, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22207 q ha hb
  have h5 (q : Pattern) (ha : d122787 q = 1) (hb : d158862 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d122787, d158862, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d122787, d158862, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d122793 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d122794 q = 1) (hb : d158863 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d122794, d158863, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d122794, d158863, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d122795 q = 1) (hb : d158864 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d122795, d158864, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d122795, d158864, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d122796 q = 1) (hb : d158865 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d122796, d158865, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d122796, d158865, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d122797 q = 1) (hb : d158866 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d122797, d158866, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d122797, d158866, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro31319 (p : Pattern) (ha : d122818 p = 1) (hb : d158875 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122755 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d122764 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d122786 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d122729 q = 1) (hb : d158861 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d122729, d158861, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31137 q ha hb
    | true =>
      simp only [d122729, d158861, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22207 q ha hb
  have h4 (q : Pattern) (ha : d122787 q = 1) (hb : d158862 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d122787, d158862, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d122787, d158862, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d122793 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d122794 q = 1) (hb : d158863 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d122794, d158863, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d122794, d158863, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d122795 q = 1) (hb : d158864 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d122795, d158864, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d122795, d158864, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d122796 q = 1) (hb : d158865 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d122796, d158865, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d122796, d158865, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d122803 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d122808 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d122810 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d122739 q = 1) (hb : d158870 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d122739, d158870, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31139 q ha hb
    | true =>
      simp only [d122739, d158870, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22210 q ha hb
  have h13 (q : Pattern) (ha : d122811 q = 1) (hb : d158871 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d122811, d158871, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
    | true =>
      simp only [d122811, d158871, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d122814 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d122815 q = 1) (hb : d158872 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d122815, d158872, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d122815, d158872, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d122816 q = 1) (hb : d158873 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d122816, d158873, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
    | true =>
      simp only [d122816, d158873, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d122817 q = 1) (hb : d158874 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d122817, d158874, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
    | true =>
      simp only [d122817, d158874, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d122818 q = 1) (hb : d158875 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d122818, d158875, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d122818, d158875, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro31320 (p : Pattern) (ha : d122838 p = 1) (hb : d159589 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d122810 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d122739 q = 1) (hb : d158870 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d122739, d158870, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31139 q ha hb
    | true =>
      simp only [d122739, d158870, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22210 q ha hb
  have h3 (q : Pattern) (ha : d122811 q = 1) (hb : d158871 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d122811, d158871, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d122811, d158871, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d122814 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d122815 q = 1) (hb : d158872 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d122815, d158872, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d122815, d158872, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d122836 q = 1) (hb : d158873 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d122836, d158873, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d122836, d158873, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d122837 q = 1) (hb : d158874 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d122837, d158874, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d122837, d158874, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d122838 q = 1) (hb : d159589 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d122838, d159589, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d122838, d159589, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro31321 (p : Pattern) (ha : d122906 p = 1) (hb : d159600 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d122890 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d122895 q = 1) (hb : d159595 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d122895, d159595, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31159 q ha hb
    | true =>
      simp only [d122895, d159595, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22241 q ha hb
  have h3 (q : Pattern) (ha : d122896 q = 1) (hb : d159596 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d122896, d159596, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d122896, d159596, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d122902 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d122903 q = 1) (hb : d159597 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d122903, d159597, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d122903, d159597, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d122904 q = 1) (hb : d159598 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d122904, d159598, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d122904, d159598, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d122905 q = 1) (hb : d159599 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d122905, d159599, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d122905, d159599, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d122906 q = 1) (hb : d159600 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d122906, d159600, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d122906, d159600, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro31322 (p : Pattern) (ha : d122919 p = 1) (hb : d159606 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122747 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d122819 q = 1) (hb : d158876 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d122819, d158876, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31318 q ha hb
    | true =>
      simp only [d122819, d158876, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31319 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d122832 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d122833 q = 1) (hb : d158877 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d122833, d158877, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d122833, d158877, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d122834 q = 1) (hb : d159587 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d122834, d159587, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d122834, d159587, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d122835 q = 1) (hb : d159588 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d122835, d159588, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d122835, d159588, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d122839 q = 1) (hb : d159590 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d122839, d159590, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d122839, d159590, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31320 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d122841 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d122842 q = 1) (hb : d159591 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d122842, d159591, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d122842, d159591, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d122843 q = 1) (hb : d159592 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d122843, d159592, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d122843, d159592, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h11 (q : Pattern) (ha : d122844 q = 1) (hb : d159593 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d122844, d159593, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d122844, d159593, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h12 (q : Pattern) (ha : d122845 q = 1) (hb : d159594 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d122845, d159594, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d122845, d159594, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d122907 q = 1) (hb : d159601 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d122907, d159601, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d122907, d159601, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31321 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d122914 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d122915 q = 1) (hb : d159602 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d122915, d159602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d122915, d159602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d122916 q = 1) (hb : d159603 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d122916, d159603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d122916, d159603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h17 (q : Pattern) (ha : d122917 q = 1) (hb : d159604 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d122917, d159604, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d122917, d159604, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h18 (q : Pattern) (ha : d122918 q = 1) (hb : d159605 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d122918, d159605, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d122918, d159605, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h19 (q : Pattern) (ha : d122919 q = 1) (hb : d159606 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d122919, d159606, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d122919, d159606, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro31323 (p : Pattern) (ha : d122925 p = 1) (hb : d159612 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d122920 q = 1) (hb : d159607 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d122920, d159607, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d122920, d159607, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31322 q ha hb
  have h2 (q : Pattern) (ha : d122921 q = 1) (hb : d159608 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d122921, d159608, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d122921, d159608, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d122922 q = 1) (hb : d159609 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d122922, d159609, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d122922, d159609, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d122923 q = 1) (hb : d159610 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d122923, d159610, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d122923, d159610, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d122924 q = 1) (hb : d159611 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d122924, d159611, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d122924, d159611, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d122925 q = 1) (hb : d159612 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d122925, d159612, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d122925, d159612, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro31324 (p : Pattern) (ha : d123056 p = 1) (hb : d159011 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d122996 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d123005 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d123037 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d122970 q = 1) (hb : d159006 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d122970, d159006, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31165 q ha hb
    | true =>
      simp only [d122970, d159006, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22251 q ha hb
  have h5 (q : Pattern) (ha : d123038 q = 1) (hb : d159007 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d123038, d159007, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d123038, d159007, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d123052 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d123053 q = 1) (hb : d159008 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d123053, d159008, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d123053, d159008, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d123054 q = 1) (hb : d159009 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d123054, d159009, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d123054, d159009, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d123055 q = 1) (hb : d159010 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d123055, d159010, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d123055, d159010, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d123056 q = 1) (hb : d159011 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d123056, d159011, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123056, d159011, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro31325 (p : Pattern) (ha : d123078 p = 1) (hb : d159020 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122996 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d123005 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d123037 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d122970 q = 1) (hb : d159006 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d122970, d159006, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31165 q ha hb
    | true =>
      simp only [d122970, d159006, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22251 q ha hb
  have h4 (q : Pattern) (ha : d123038 q = 1) (hb : d159007 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d123038, d159007, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d123038, d159007, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d123052 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d123053 q = 1) (hb : d159008 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d123053, d159008, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d123053, d159008, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d123054 q = 1) (hb : d159009 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d123054, d159009, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d123054, d159009, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d123055 q = 1) (hb : d159010 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d123055, d159010, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123055, d159010, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d123062 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d123067 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d123070 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d122980 q = 1) (hb : d159015 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d122980, d159015, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31167 q ha hb
    | true =>
      simp only [d122980, d159015, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22254 q ha hb
  have h13 (q : Pattern) (ha : d123071 q = 1) (hb : d159016 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d123071, d159016, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
    | true =>
      simp only [d123071, d159016, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d123074 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d123075 q = 1) (hb : d159017 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d123075, d159017, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d123075, d159017, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d123076 q = 1) (hb : d159018 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d123076, d159018, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
    | true =>
      simp only [d123076, d159018, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d123077 q = 1) (hb : d159019 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d123077, d159019, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
    | true =>
      simp only [d123077, d159019, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d123078 q = 1) (hb : d159020 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d123078, d159020, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d123078, d159020, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro31326 (p : Pattern) (ha : d123103 p = 1) (hb : d159617 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d123070 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d122980 q = 1) (hb : d159015 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d122980, d159015, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31167 q ha hb
    | true =>
      simp only [d122980, d159015, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22254 q ha hb
  have h3 (q : Pattern) (ha : d123071 q = 1) (hb : d159016 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d123071, d159016, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d123071, d159016, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d123074 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d123075 q = 1) (hb : d159017 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d123075, d159017, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d123075, d159017, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d123101 q = 1) (hb : d159018 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d123101, d159018, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123101, d159018, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d123102 q = 1) (hb : d159019 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d123102, d159019, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123102, d159019, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d123103 q = 1) (hb : d159617 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d123103, d159617, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123103, d159617, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro31327 (p : Pattern) (ha : d123182 p = 1) (hb : d159133 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d123141 q = 1) (hb : d124602 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d123141, d124602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22282 q ha hb
    | true =>
      simp only [d123141, d124602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22283 q ha hb
  have h2 (q : Pattern) (ha : d123142 q = 1) (hb : d124603 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d123142, d124603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123142, d124603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d123143 q = 1) (hb : d124604 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d123143, d124604, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123143, d124604, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d123150 q = 1) (hb : d124610 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d123150, d124610, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22283 q ha hb
    | true =>
      simp only [d123150, d124610, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22285 q hb ha
  have h5 (q : Pattern) (ha : d123151 q = 1) (hb : d124611 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d123151, d124611, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123151, d124611, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d123152 q = 1) (hb : d124612 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d123152, d124612, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123152, d124612, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d123153 q = 1) (hb : d159113 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d123153, d159113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d123153, d159113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d123168 q = 1) (hb : d124622 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d123168, d124622, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22283 q ha hb
    | true =>
      simp only [d123168, d124622, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22288 q hb ha
  have h9 (q : Pattern) (ha : d123169 q = 1) (hb : d124623 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d123169, d124623, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123169, d124623, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d123170 q = 1) (hb : d124624 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d123170, d124624, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123170, d124624, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d123171 q = 1) (hb : d124625 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d123171, d124625, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d123171, d124625, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d123181 q = 1) (hb : d159132 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d123181, d159132, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d123181, d159132, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d123182 q = 1) (hb : d159133 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d123182, d159133, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d123182, d159133, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h13 p ha hb
theorem andIntro31328 (p : Pattern) (ha : d123188 p = 1) (hb : d159626 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d123183 q = 1) (hb : d159134 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d123183, d159134, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31327 q ha hb
    | true =>
      simp only [d123183, d159134, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d123184 q = 1) (hb : d159135 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d123184, d159135, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123184, d159135, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d123174 q = 1) (hb : d124628 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d123174, d124628, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22289 q ha hb
    | true =>
      simp only [d123174, d124628, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d123175 q = 1) (hb : d124629 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d123175, d124629, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123175, d124629, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d123185 q = 1) (hb : d159623 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d123185, d159623, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d123185, d159623, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d123186 q = 1) (hb : d159624 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d123186, d159624, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d123186, d159624, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d123187 q = 1) (hb : d159625 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d123187, d159625, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d123187, d159625, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d123188 q = 1) (hb : d159626 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d123188, d159626, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d123188, d159626, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro31329 (p : Pattern) (ha : d123212 p = 1) (hb : d159632 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d123180 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d123193 q = 1) (hb : d159627 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d123193, d159627, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31328 q ha hb
    | true =>
      simp only [d123193, d159627, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22294 q ha hb
  have h3 (q : Pattern) (ha : d123194 q = 1) (hb : d159628 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d123194, d159628, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d123194, d159628, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d123208 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d123209 q = 1) (hb : d159629 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d123209, d159629, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d123209, d159629, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d123210 q = 1) (hb : d159630 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d123210, d159630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123210, d159630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d123211 q = 1) (hb : d159631 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d123211, d159631, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123211, d159631, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d123212 q = 1) (hb : d159632 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d123212, d159632, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123212, d159632, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro31330 (p : Pattern) (ha : d123225 p = 1) (hb : d159638 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122988 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d123079 q = 1) (hb : d159021 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d123079, d159021, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31324 q ha hb
    | true =>
      simp only [d123079, d159021, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31325 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d123097 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d123098 q = 1) (hb : d159022 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d123098, d159022, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d123098, d159022, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d123099 q = 1) (hb : d159615 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d123099, d159615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d123099, d159615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d123100 q = 1) (hb : d159616 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d123100, d159616, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123100, d159616, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d123104 q = 1) (hb : d159618 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d123104, d159618, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d123104, d159618, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31326 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d123106 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d123107 q = 1) (hb : d159619 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d123107, d159619, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d123107, d159619, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d123108 q = 1) (hb : d159620 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d123108, d159620, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d123108, d159620, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h11 (q : Pattern) (ha : d123109 q = 1) (hb : d159621 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d123109, d159621, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d123109, d159621, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h12 (q : Pattern) (ha : d123110 q = 1) (hb : d159622 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d123110, d159622, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d123110, d159622, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d123213 q = 1) (hb : d159633 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d123213, d159633, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d123213, d159633, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31329 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d123220 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d123221 q = 1) (hb : d159634 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d123221, d159634, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d123221, d159634, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d123222 q = 1) (hb : d159635 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d123222, d159635, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d123222, d159635, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h17 (q : Pattern) (ha : d123223 q = 1) (hb : d159636 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d123223, d159636, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d123223, d159636, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h18 (q : Pattern) (ha : d123224 q = 1) (hb : d159637 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d123224, d159637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d123224, d159637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h19 (q : Pattern) (ha : d123225 q = 1) (hb : d159638 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d123225, d159638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d123225, d159638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro31331 (p : Pattern) (ha : d123231 p = 1) (hb : d159644 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d123226 q = 1) (hb : d159639 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d123226, d159639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123226, d159639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31330 q ha hb
  have h2 (q : Pattern) (ha : d123227 q = 1) (hb : d159640 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d123227, d159640, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123227, d159640, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d123228 q = 1) (hb : d159641 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d123228, d159641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123228, d159641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d123229 q = 1) (hb : d159642 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d123229, d159642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123229, d159642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d123230 q = 1) (hb : d159643 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d123230, d159643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123230, d159643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d123231 q = 1) (hb : d159644 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d123231, d159644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123231, d159644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro31332 (p : Pattern) (ha : d123363 p = 1) (hb : d159175 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d123303 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d123312 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d123344 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d123277 q = 1) (hb : d159170 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d123277, d159170, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31198 q ha hb
    | true =>
      simp only [d123277, d159170, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22304 q ha hb
  have h5 (q : Pattern) (ha : d123345 q = 1) (hb : d159171 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d123345, d159171, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d123345, d159171, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d123359 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d123360 q = 1) (hb : d159172 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d123360, d159172, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d123360, d159172, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d123361 q = 1) (hb : d159173 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d123361, d159173, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d123361, d159173, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d123362 q = 1) (hb : d159174 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d123362, d159174, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d123362, d159174, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d123363 q = 1) (hb : d159175 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d123363, d159175, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123363, d159175, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro31333 (p : Pattern) (ha : d123385 p = 1) (hb : d159184 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d123303 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d123312 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d123344 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d123277 q = 1) (hb : d159170 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d123277, d159170, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31198 q ha hb
    | true =>
      simp only [d123277, d159170, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22304 q ha hb
  have h4 (q : Pattern) (ha : d123345 q = 1) (hb : d159171 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d123345, d159171, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d123345, d159171, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d123359 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d123360 q = 1) (hb : d159172 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d123360, d159172, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d123360, d159172, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d123361 q = 1) (hb : d159173 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d123361, d159173, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d123361, d159173, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d123362 q = 1) (hb : d159174 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d123362, d159174, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123362, d159174, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d123369 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d123374 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d123377 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d123287 q = 1) (hb : d159179 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d123287, d159179, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31200 q ha hb
    | true =>
      simp only [d123287, d159179, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22307 q ha hb
  have h13 (q : Pattern) (ha : d123378 q = 1) (hb : d159180 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d123378, d159180, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
    | true =>
      simp only [d123378, d159180, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d123381 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d123382 q = 1) (hb : d159181 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d123382, d159181, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d123382, d159181, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d123383 q = 1) (hb : d159182 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d123383, d159182, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
    | true =>
      simp only [d123383, d159182, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d123384 q = 1) (hb : d159183 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d123384, d159183, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
    | true =>
      simp only [d123384, d159183, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d123385 q = 1) (hb : d159184 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d123385, d159184, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d123385, d159184, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro31334 (p : Pattern) (ha : d123410 p = 1) (hb : d159650 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d123377 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d123287 q = 1) (hb : d159179 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d123287, d159179, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31200 q ha hb
    | true =>
      simp only [d123287, d159179, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22307 q ha hb
  have h3 (q : Pattern) (ha : d123378 q = 1) (hb : d159180 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d123378, d159180, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d123378, d159180, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d123381 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d123382 q = 1) (hb : d159181 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d123382, d159181, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d123382, d159181, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d123408 q = 1) (hb : d159182 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d123408, d159182, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123408, d159182, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d123409 q = 1) (hb : d159183 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d123409, d159183, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123409, d159183, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d123410 q = 1) (hb : d159650 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d123410, d159650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123410, d159650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro31335 (p : Pattern) (ha : d123489 p = 1) (hb : d159297 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d123448 q = 1) (hb : d124836 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d123448, d124836, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22335 q ha hb
    | true =>
      simp only [d123448, d124836, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22336 q ha hb
  have h2 (q : Pattern) (ha : d123449 q = 1) (hb : d124837 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d123449, d124837, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123449, d124837, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d123450 q = 1) (hb : d124838 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d123450, d124838, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123450, d124838, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d123457 q = 1) (hb : d124844 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d123457, d124844, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22336 q ha hb
    | true =>
      simp only [d123457, d124844, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22338 q hb ha
  have h5 (q : Pattern) (ha : d123458 q = 1) (hb : d124845 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d123458, d124845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123458, d124845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d123459 q = 1) (hb : d124846 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d123459, d124846, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123459, d124846, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d123460 q = 1) (hb : d159277 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d123460, d159277, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d123460, d159277, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d123475 q = 1) (hb : d124856 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d123475, d124856, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22336 q ha hb
    | true =>
      simp only [d123475, d124856, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22341 q hb ha
  have h9 (q : Pattern) (ha : d123476 q = 1) (hb : d124857 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d123476, d124857, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123476, d124857, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d123477 q = 1) (hb : d124858 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d123477, d124858, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123477, d124858, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d123478 q = 1) (hb : d124859 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d123478, d124859, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d123478, d124859, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d123488 q = 1) (hb : d159296 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d123488, d159296, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d123488, d159296, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d123489 q = 1) (hb : d159297 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d123489, d159297, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d123489, d159297, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h13 p ha hb
theorem andIntro31336 (p : Pattern) (ha : d123495 p = 1) (hb : d159659 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d123490 q = 1) (hb : d159298 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d123490, d159298, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31335 q ha hb
    | true =>
      simp only [d123490, d159298, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d123491 q = 1) (hb : d159299 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d123491, d159299, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123491, d159299, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d123481 q = 1) (hb : d124862 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d123481, d124862, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22342 q ha hb
    | true =>
      simp only [d123481, d124862, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d123482 q = 1) (hb : d124863 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d123482, d124863, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123482, d124863, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d123492 q = 1) (hb : d159656 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d123492, d159656, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d123492, d159656, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d123493 q = 1) (hb : d159657 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d123493, d159657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d123493, d159657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d123494 q = 1) (hb : d159658 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d123494, d159658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d123494, d159658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d123495 q = 1) (hb : d159659 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d123495, d159659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d123495, d159659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro31337 (p : Pattern) (ha : d123519 p = 1) (hb : d159665 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d123487 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d123500 q = 1) (hb : d159660 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d123500, d159660, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31336 q ha hb
    | true =>
      simp only [d123500, d159660, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22347 q ha hb
  have h3 (q : Pattern) (ha : d123501 q = 1) (hb : d159661 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d123501, d159661, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d123501, d159661, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d123515 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d123516 q = 1) (hb : d159662 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d123516, d159662, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d123516, d159662, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d123517 q = 1) (hb : d159663 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d123517, d159663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123517, d159663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d123518 q = 1) (hb : d159664 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d123518, d159664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123518, d159664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d123519 q = 1) (hb : d159665 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d123519, d159665, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123519, d159665, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro31338 (p : Pattern) (ha : d123532 p = 1) (hb : d159671 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d123295 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d123386 q = 1) (hb : d159185 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d123386, d159185, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31332 q ha hb
    | true =>
      simp only [d123386, d159185, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31333 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d123404 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d123405 q = 1) (hb : d159186 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d123405, d159186, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d123405, d159186, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d123406 q = 1) (hb : d159648 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d123406, d159648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d123406, d159648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d123407 q = 1) (hb : d159649 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d123407, d159649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123407, d159649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d123411 q = 1) (hb : d159651 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d123411, d159651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d123411, d159651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31334 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d123413 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d123414 q = 1) (hb : d159652 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d123414, d159652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d123414, d159652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d123415 q = 1) (hb : d159653 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d123415, d159653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d123415, d159653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h11 (q : Pattern) (ha : d123416 q = 1) (hb : d159654 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d123416, d159654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d123416, d159654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h12 (q : Pattern) (ha : d123417 q = 1) (hb : d159655 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d123417, d159655, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d123417, d159655, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d123520 q = 1) (hb : d159666 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d123520, d159666, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d123520, d159666, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31337 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d123527 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d123528 q = 1) (hb : d159667 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d123528, d159667, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d123528, d159667, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d123529 q = 1) (hb : d159668 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d123529, d159668, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d123529, d159668, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h17 (q : Pattern) (ha : d123530 q = 1) (hb : d159669 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d123530, d159669, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d123530, d159669, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h18 (q : Pattern) (ha : d123531 q = 1) (hb : d159670 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d123531, d159670, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d123531, d159670, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h19 (q : Pattern) (ha : d123532 q = 1) (hb : d159671 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d123532, d159671, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d123532, d159671, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro31339 (p : Pattern) (ha : d123538 p = 1) (hb : d159677 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d123533 q = 1) (hb : d159672 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d123533, d159672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123533, d159672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31338 q ha hb
  have h2 (q : Pattern) (ha : d123534 q = 1) (hb : d159673 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d123534, d159673, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123534, d159673, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d123535 q = 1) (hb : d159674 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d123535, d159674, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123535, d159674, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d123536 q = 1) (hb : d159675 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d123536, d159675, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123536, d159675, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d123537 q = 1) (hb : d159676 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d123537, d159676, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123537, d159676, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d123538 q = 1) (hb : d159677 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d123538, d159677, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123538, d159677, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro31340 (p : Pattern) (ha : d123665 p = 1) (hb : d159340 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d123609 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d123618 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d123646 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d123583 q = 1) (hb : d159335 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d123583, d159335, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31231 q ha hb
    | true =>
      simp only [d123583, d159335, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22357 q ha hb
  have h5 (q : Pattern) (ha : d123647 q = 1) (hb : d159336 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d123647, d159336, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d123647, d159336, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d123661 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d123662 q = 1) (hb : d159337 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d123662, d159337, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d123662, d159337, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d123663 q = 1) (hb : d159338 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d123663, d159338, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d123663, d159338, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d123664 q = 1) (hb : d159339 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d123664, d159339, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d123664, d159339, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d123665 q = 1) (hb : d159340 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d123665, d159340, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123665, d159340, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro31341 (p : Pattern) (ha : d123687 p = 1) (hb : d159349 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d123609 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d123618 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d123646 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d123583 q = 1) (hb : d159335 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d123583, d159335, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31231 q ha hb
    | true =>
      simp only [d123583, d159335, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22357 q ha hb
  have h4 (q : Pattern) (ha : d123647 q = 1) (hb : d159336 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d123647, d159336, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d123647, d159336, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d123661 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d123662 q = 1) (hb : d159337 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d123662, d159337, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d123662, d159337, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d123663 q = 1) (hb : d159338 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d123663, d159338, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d123663, d159338, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d123664 q = 1) (hb : d159339 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d123664, d159339, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123664, d159339, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d123671 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d123676 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d123679 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d123593 q = 1) (hb : d159344 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d123593, d159344, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31233 q ha hb
    | true =>
      simp only [d123593, d159344, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22360 q ha hb
  have h13 (q : Pattern) (ha : d123680 q = 1) (hb : d159345 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d123680, d159345, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
    | true =>
      simp only [d123680, d159345, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d123683 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d123684 q = 1) (hb : d159346 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d123684, d159346, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d123684, d159346, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d123685 q = 1) (hb : d159347 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d123685, d159347, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
    | true =>
      simp only [d123685, d159347, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d123686 q = 1) (hb : d159348 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d123686, d159348, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
    | true =>
      simp only [d123686, d159348, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d123687 q = 1) (hb : d159349 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d123687, d159349, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d123687, d159349, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro31342 (p : Pattern) (ha : d123712 p = 1) (hb : d159684 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d123679 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d123593 q = 1) (hb : d159344 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d123593, d159344, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31233 q ha hb
    | true =>
      simp only [d123593, d159344, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22360 q ha hb
  have h3 (q : Pattern) (ha : d123680 q = 1) (hb : d159345 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d123680, d159345, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d123680, d159345, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d123683 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d123684 q = 1) (hb : d159346 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d123684, d159346, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d123684, d159346, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d123710 q = 1) (hb : d159347 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d123710, d159347, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123710, d159347, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d123711 q = 1) (hb : d159348 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d123711, d159348, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123711, d159348, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d123712 q = 1) (hb : d159684 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d123712, d159684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123712, d159684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro31343 (p : Pattern) (ha : d123781 p = 1) (hb : d159462 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d123740 q = 1) (hb : d125069 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d123740, d125069, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22388 q ha hb
    | true =>
      simp only [d123740, d125069, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22389 q ha hb
  have h2 (q : Pattern) (ha : d123741 q = 1) (hb : d125070 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d123741, d125070, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123741, d125070, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d123742 q = 1) (hb : d125071 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d123742, d125071, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123742, d125071, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d123749 q = 1) (hb : d125077 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d123749, d125077, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22389 q ha hb
    | true =>
      simp only [d123749, d125077, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22391 q hb ha
  have h5 (q : Pattern) (ha : d123750 q = 1) (hb : d125078 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d123750, d125078, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123750, d125078, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d123751 q = 1) (hb : d125079 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d123751, d125079, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123751, d125079, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d123752 q = 1) (hb : d159442 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d123752, d159442, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d123752, d159442, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d123767 q = 1) (hb : d125089 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d123767, d125089, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22389 q ha hb
    | true =>
      simp only [d123767, d125089, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22394 q hb ha
  have h9 (q : Pattern) (ha : d123768 q = 1) (hb : d125090 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d123768, d125090, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123768, d125090, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d123769 q = 1) (hb : d125091 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d123769, d125091, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123769, d125091, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d123770 q = 1) (hb : d125092 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d123770, d125092, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d123770, d125092, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d123780 q = 1) (hb : d159461 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d123780, d159461, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d123780, d159461, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d123781 q = 1) (hb : d159462 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d123781, d159462, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d123781, d159462, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h13 p ha hb
theorem andIntro31344 (p : Pattern) (ha : d123787 p = 1) (hb : d159693 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d123782 q = 1) (hb : d159463 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d123782, d159463, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31343 q ha hb
    | true =>
      simp only [d123782, d159463, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d123783 q = 1) (hb : d159464 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d123783, d159464, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123783, d159464, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d123773 q = 1) (hb : d125095 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d123773, d125095, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22395 q ha hb
    | true =>
      simp only [d123773, d125095, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d123774 q = 1) (hb : d125096 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d123774, d125096, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123774, d125096, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d123784 q = 1) (hb : d159690 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d123784, d159690, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d123784, d159690, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d123785 q = 1) (hb : d159691 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d123785, d159691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d123785, d159691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d123786 q = 1) (hb : d159692 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d123786, d159692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d123786, d159692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d123787 q = 1) (hb : d159693 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d123787, d159693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d123787, d159693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro31345 (p : Pattern) (ha : d123811 p = 1) (hb : d159699 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d123779 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d123792 q = 1) (hb : d159694 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d123792, d159694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31344 q ha hb
    | true =>
      simp only [d123792, d159694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22400 q ha hb
  have h3 (q : Pattern) (ha : d123793 q = 1) (hb : d159695 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d123793, d159695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d123793, d159695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d123807 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d123808 q = 1) (hb : d159696 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d123808, d159696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d123808, d159696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d123809 q = 1) (hb : d159697 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d123809, d159697, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123809, d159697, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d123810 q = 1) (hb : d159698 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d123810, d159698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123810, d159698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d123811 q = 1) (hb : d159699 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d123811, d159699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123811, d159699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro31346 (p : Pattern) (ha : d123824 p = 1) (hb : d159705 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d123601 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d123688 q = 1) (hb : d159350 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d123688, d159350, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31340 q ha hb
    | true =>
      simp only [d123688, d159350, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31341 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d123706 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d123707 q = 1) (hb : d159351 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d123707, d159351, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d123707, d159351, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d123708 q = 1) (hb : d159682 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d123708, d159682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d123708, d159682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d123709 q = 1) (hb : d159683 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d123709, d159683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123709, d159683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d123713 q = 1) (hb : d159685 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d123713, d159685, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d123713, d159685, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31342 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d123715 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d123716 q = 1) (hb : d159686 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d123716, d159686, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d123716, d159686, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d123717 q = 1) (hb : d159687 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d123717, d159687, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d123717, d159687, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h11 (q : Pattern) (ha : d123718 q = 1) (hb : d159688 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d123718, d159688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d123718, d159688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h12 (q : Pattern) (ha : d123719 q = 1) (hb : d159689 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d123719, d159689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d123719, d159689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d123812 q = 1) (hb : d159700 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d123812, d159700, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d123812, d159700, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31345 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d123819 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d123820 q = 1) (hb : d159701 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d123820, d159701, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d123820, d159701, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d123821 q = 1) (hb : d159702 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d123821, d159702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d123821, d159702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h17 (q : Pattern) (ha : d123822 q = 1) (hb : d159703 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d123822, d159703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d123822, d159703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h18 (q : Pattern) (ha : d123823 q = 1) (hb : d159704 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d123823, d159704, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d123823, d159704, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h19 (q : Pattern) (ha : d123824 q = 1) (hb : d159705 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d123824, d159705, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d123824, d159705, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro31347 (p : Pattern) (ha : d123830 p = 1) (hb : d159711 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d123825 q = 1) (hb : d159706 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d123825, d159706, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123825, d159706, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31346 q ha hb
  have h2 (q : Pattern) (ha : d123826 q = 1) (hb : d159707 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d123826, d159707, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123826, d159707, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d123827 q = 1) (hb : d159708 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d123827, d159708, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123827, d159708, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d123828 q = 1) (hb : d159709 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d123828, d159709, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123828, d159709, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d123829 q = 1) (hb : d159710 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d123829, d159710, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123829, d159710, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d123830 q = 1) (hb : d159711 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d123830, d159711, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123830, d159711, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro31348 (p : Pattern) (ha : d123836 p = 1) (hb : d159717 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d122703 q = 1) (hb : d159586 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d122703, d159586, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31311 q ha hb
    | true =>
      simp only [d122703, d159586, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31317 q ha hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d122926 q = 1) (hb : d159613 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d122926, d159613, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d122926, d159613, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31323 q ha hb
  have h3 (q : Pattern) (ha : d122927 q = 1) (hb : d159614 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d122927, d159614, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d122927, d159614, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d123232 q = 1) (hb : d159645 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d123232, d159645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d123232, d159645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31331 q ha hb
  have h5 (q : Pattern) (ha : d123233 q = 1) (hb : d159646 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d123233, d159646, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d123233, d159646, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d123234 q = 1) (hb : d159647 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d123234, d159647, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d123234, d159647, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d123539 q = 1) (hb : d159678 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d123539, d159678, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d123539, d159678, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31339 q ha hb
  have h8 (q : Pattern) (ha : d123540 q = 1) (hb : d159679 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d123540, d159679, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d123540, d159679, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d123541 q = 1) (hb : d159680 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d123541, d159680, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d123541, d159680, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d123542 q = 1) (hb : d159681 q = 1) : d0 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d123542, d159681, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d123542, d159681, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d123831 q = 1) (hb : d159712 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d123831, d159712, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d123831, d159712, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31347 q ha hb
  have h12 (q : Pattern) (ha : d123832 q = 1) (hb : d159713 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d123832, d159713, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d123832, d159713, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d123833 q = 1) (hb : d159714 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d123833, d159714, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d123833, d159714, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d123834 q = 1) (hb : d159715 q = 1) : d0 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d123834, d159715, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d123834, d159715, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d123835 q = 1) (hb : d159716 q = 1) : d0 q = 1 := by
    cases bit : q 10250 with
    | false =>
      simp only [d123835, d159716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d123835, d159716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d123836 q = 1) (hb : d159717 q = 1) : d0 q = 1 := by
    cases bit : q 260 with
    | false =>
      simp only [d123836, d159717, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d123836, d159717, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  exact h16 p ha hb
theorem andIntro31349 (p : Pattern) (ha : d123842 p = 1) (hb : d159723 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d123837 q = 1) (hb : d159718 q = 1) : d0 q = 1 := by
    cases bit : q 259 with
    | false =>
      simp only [d123837, d159718, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31348 q ha hb
    | true =>
      simp only [d123837, d159718, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d123838 q = 1) (hb : d159719 q = 1) : d0 q = 1 := by
    cases bit : q 258 with
    | false =>
      simp only [d123838, d159719, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d123838, d159719, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d123839 q = 1) (hb : d159720 q = 1) : d0 q = 1 := by
    cases bit : q 257 with
    | false =>
      simp only [d123839, d159720, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d123839, d159720, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d123840 q = 1) (hb : d159721 q = 1) : d0 q = 1 := by
    cases bit : q 256 with
    | false =>
      simp only [d123840, d159721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d123840, d159721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d123841 q = 1) (hb : d159722 q = 1) : d0 q = 1 := by
    cases bit : q 255 with
    | false =>
      simp only [d123841, d159722, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d123841, d159722, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d123842 q = 1) (hb : d159723 q = 1) : d0 q = 1 := by
    cases bit : q 254 with
    | false =>
      simp only [d123842, d159723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d123842, d159723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro31350 (p : Pattern) (ha : d123848 p = 1) (hb : d159729 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d123843 q = 1) (hb : d159724 q = 1) : d0 q = 1 := by
    cases bit : q 253 with
    | false =>
      simp only [d123843, d159724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31349 q ha hb
    | true =>
      simp only [d123843, d159724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d123844 q = 1) (hb : d159725 q = 1) : d0 q = 1 := by
    cases bit : q 252 with
    | false =>
      simp only [d123844, d159725, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d123844, d159725, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d123845 q = 1) (hb : d159726 q = 1) : d0 q = 1 := by
    cases bit : q 251 with
    | false =>
      simp only [d123845, d159726, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d123845, d159726, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d123846 q = 1) (hb : d159727 q = 1) : d0 q = 1 := by
    cases bit : q 250 with
    | false =>
      simp only [d123846, d159727, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d123846, d159727, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d123847 q = 1) (hb : d159728 q = 1) : d0 q = 1 := by
    cases bit : q 249 with
    | false =>
      simp only [d123847, d159728, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d123847, d159728, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d123848 q = 1) (hb : d159729 q = 1) : d0 q = 1 := by
    cases bit : q 245 with
    | false =>
      simp only [d123848, d159729, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d123848, d159729, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro31351 (p : Pattern) (ha : d123854 p = 1) (hb : d159735 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d123849 q = 1) (hb : d159730 q = 1) : d0 q = 1 := by
    cases bit : q 200 with
    | false =>
      simp only [d123849, d159730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31350 q ha hb
    | true =>
      simp only [d123849, d159730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d123850 q = 1) (hb : d159731 q = 1) : d0 q = 1 := by
    cases bit : q 199 with
    | false =>
      simp only [d123850, d159731, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d123850, d159731, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d123851 q = 1) (hb : d159732 q = 1) : d0 q = 1 := by
    cases bit : q 186 with
    | false =>
      simp only [d123851, d159732, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d123851, d159732, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d123852 q = 1) (hb : d159733 q = 1) : d0 q = 1 := by
    cases bit : q 185 with
    | false =>
      simp only [d123852, d159733, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d123852, d159733, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d123853 q = 1) (hb : d159734 q = 1) : d0 q = 1 := by
    cases bit : q 184 with
    | false =>
      simp only [d123853, d159734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d123853, d159734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d123854 q = 1) (hb : d159735 q = 1) : d0 q = 1 := by
    cases bit : q 181 with
    | false =>
      simp only [d123854, d159735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d123854, d159735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro31352 (p : Pattern) (ha : d123860 p = 1) (hb : d159741 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d123855 q = 1) (hb : d159736 q = 1) : d0 q = 1 := by
    cases bit : q 177 with
    | false =>
      simp only [d123855, d159736, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31351 q ha hb
    | true =>
      simp only [d123855, d159736, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d123856 q = 1) (hb : d159737 q = 1) : d0 q = 1 := by
    cases bit : q 164 with
    | false =>
      simp only [d123856, d159737, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d123856, d159737, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d123857 q = 1) (hb : d159738 q = 1) : d0 q = 1 := by
    cases bit : q 156 with
    | false =>
      simp only [d123857, d159738, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d123857, d159738, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d123858 q = 1) (hb : d159739 q = 1) : d0 q = 1 := by
    cases bit : q 155 with
    | false =>
      simp only [d123858, d159739, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d123858, d159739, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d123859 q = 1) (hb : d159740 q = 1) : d0 q = 1 := by
    cases bit : q 134 with
    | false =>
      simp only [d123859, d159740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d123859, d159740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d123860 q = 1) (hb : d159741 q = 1) : d0 q = 1 := by
    cases bit : q 133 with
    | false =>
      simp only [d123860, d159741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d123860, d159741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro31353 (p : Pattern) (ha : d123866 p = 1) (hb : d159747 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d123861 q = 1) (hb : d159742 q = 1) : d0 q = 1 := by
    cases bit : q 120 with
    | false =>
      simp only [d123861, d159742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31352 q ha hb
    | true =>
      simp only [d123861, d159742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d123862 q = 1) (hb : d159743 q = 1) : d0 q = 1 := by
    cases bit : q 118 with
    | false =>
      simp only [d123862, d159743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d123862, d159743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d123863 q = 1) (hb : d159744 q = 1) : d0 q = 1 := by
    cases bit : q 114 with
    | false =>
      simp only [d123863, d159744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d123863, d159744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d123864 q = 1) (hb : d159745 q = 1) : d0 q = 1 := by
    cases bit : q 111 with
    | false =>
      simp only [d123864, d159745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d123864, d159745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d123865 q = 1) (hb : d159746 q = 1) : d0 q = 1 := by
    cases bit : q 98 with
    | false =>
      simp only [d123865, d159746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d123865, d159746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d123866 q = 1) (hb : d159747 q = 1) : d0 q = 1 := by
    cases bit : q 97 with
    | false =>
      simp only [d123866, d159747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d123866, d159747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro31354 (p : Pattern) (ha : d123872 p = 1) (hb : d159753 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d123867 q = 1) (hb : d159748 q = 1) : d0 q = 1 := by
    cases bit : q 94 with
    | false =>
      simp only [d123867, d159748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31353 q ha hb
    | true =>
      simp only [d123867, d159748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d123868 q = 1) (hb : d159749 q = 1) : d0 q = 1 := by
    cases bit : q 76 with
    | false =>
      simp only [d123868, d159749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d123868, d159749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d123869 q = 1) (hb : d159750 q = 1) : d0 q = 1 := by
    cases bit : q 67 with
    | false =>
      simp only [d123869, d159750, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d123869, d159750, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d123870 q = 1) (hb : d159751 q = 1) : d0 q = 1 := by
    cases bit : q 52 with
    | false =>
      simp only [d123870, d159751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d123870, d159751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d123871 q = 1) (hb : d159752 q = 1) : d0 q = 1 := by
    cases bit : q 47 with
    | false =>
      simp only [d123871, d159752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d123871, d159752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d123872 q = 1) (hb : d159753 q = 1) : d0 q = 1 := by
    cases bit : q 46 with
    | false =>
      simp only [d123872, d159753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d123872, d159753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro31355 (p : Pattern) (ha : d123878 p = 1) (hb : d159759 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d123873 q = 1) (hb : d159754 q = 1) : d0 q = 1 := by
    cases bit : q 45 with
    | false =>
      simp only [d123873, d159754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31354 q ha hb
    | true =>
      simp only [d123873, d159754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d123874 q = 1) (hb : d159755 q = 1) : d0 q = 1 := by
    cases bit : q 30 with
    | false =>
      simp only [d123874, d159755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d123874, d159755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d123875 q = 1) (hb : d159756 q = 1) : d0 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d123875, d159756, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d123875, d159756, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d123876 q = 1) (hb : d159757 q = 1) : d0 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d123876, d159757, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d123876, d159757, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d123877 q = 1) (hb : d159758 q = 1) : d0 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d123877, d159758, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d123877, d159758, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d123878 q = 1) (hb : d159759 q = 1) : d0 q = 1 := by
    cases bit : q 25 with
    | false =>
      simp only [d123878, d159759, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d123878, d159759, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro31356 (p : Pattern) (ha : d125455 p = 1) (hb : d158600 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d14070 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d14076 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d14092 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d158545 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d125451 q = 1) (hb : d158596 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d125451, d158596, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d125451, d158596, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d14114 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d125452 q = 1) (hb : d158597 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d125452, d158597, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d125452, d158597, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d125453 q = 1) (hb : d158598 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d125453, d158598, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d125453, d158598, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d125454 q = 1) (hb : d158599 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d125454, d158599, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d125454, d158599, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d125455 q = 1) (hb : d158600 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d125455, d158600, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d125455, d158600, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro31357 (p : Pattern) (ha : d125460 p = 1) (hb : d158607 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d14070 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d14076 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d14092 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d158545 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d125451 q = 1) (hb : d158596 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d125451, d158596, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d125451, d158596, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d14114 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d125452 q = 1) (hb : d158597 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d125452, d158597, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d125452, d158597, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d125453 q = 1) (hb : d158598 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d125453, d158598, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d125453, d158598, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d125454 q = 1) (hb : d158599 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d125454, d158599, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d125454, d158599, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d14123 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d14127 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d14129 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d158552 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d125456 q = 1) (hb : d158603 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d125456, d158603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
    | true =>
      simp only [d125456, d158603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d14135 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d125457 q = 1) (hb : d158604 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d125457, d158604, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d125457, d158604, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d125458 q = 1) (hb : d158605 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d125458, d158605, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
    | true =>
      simp only [d125458, d158605, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d125459 q = 1) (hb : d158606 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d125459, d158606, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
    | true =>
      simp only [d125459, d158606, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d125460 q = 1) (hb : d158607 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d125460, d158607, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d125460, d158607, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro31358 (p : Pattern) (ha : d125467 p = 1) (hb : d159537 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d14129 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d158552 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d125456 q = 1) (hb : d158603 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d125456, d158603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d125456, d158603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d14135 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d125457 q = 1) (hb : d158604 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d125457, d158604, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d125457, d158604, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d125465 q = 1) (hb : d158605 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d125465, d158605, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d125465, d158605, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d125466 q = 1) (hb : d158606 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d125466, d158606, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d125466, d158606, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d125467 q = 1) (hb : d159537 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d125467, d159537, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d125467, d159537, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro31359 (p : Pattern) (ha : d125477 p = 1) (hb : d159547 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d14169 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d158579 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d125473 q = 1) (hb : d159543 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d125473, d159543, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d125473, d159543, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d14191 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d125474 q = 1) (hb : d159544 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d125474, d159544, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d125474, d159544, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d125475 q = 1) (hb : d159545 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d125475, d159545, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d125475, d159545, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d125476 q = 1) (hb : d159546 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d125476, d159546, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d125476, d159546, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d125477 q = 1) (hb : d159547 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d125477, d159547, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d125477, d159547, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro31360 (p : Pattern) (ha : d125483 p = 1) (hb : d159553 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d14064 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d125461 q = 1) (hb : d158608 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d125461, d158608, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31356 q ha hb
    | true =>
      simp only [d125461, d158608, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31357 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d14142 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d125462 q = 1) (hb : d158609 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d125462, d158609, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d125462, d158609, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d125463 q = 1) (hb : d159535 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d125463, d159535, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d125463, d159535, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d125464 q = 1) (hb : d159536 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d125464, d159536, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d125464, d159536, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d125468 q = 1) (hb : d159538 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d125468, d159538, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d125468, d159538, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31358 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d407 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d125469 q = 1) (hb : d159539 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d125469, d159539, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d125469, d159539, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d125470 q = 1) (hb : d159540 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d125470, d159540, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d125470, d159540, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h11 (q : Pattern) (ha : d125471 q = 1) (hb : d159541 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d125471, d159541, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d125471, d159541, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h12 (q : Pattern) (ha : d125472 q = 1) (hb : d159542 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d125472, d159542, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d125472, d159542, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d125478 q = 1) (hb : d159548 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d125478, d159548, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d125478, d159548, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31359 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d463 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d125479 q = 1) (hb : d159549 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d125479, d159549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d125479, d159549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d125480 q = 1) (hb : d159550 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d125480, d159550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d125480, d159550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h17 (q : Pattern) (ha : d125481 q = 1) (hb : d159551 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d125481, d159551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d125481, d159551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h18 (q : Pattern) (ha : d125482 q = 1) (hb : d159552 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d125482, d159552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d125482, d159552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h19 (q : Pattern) (ha : d125483 q = 1) (hb : d159553 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d125483, d159553, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d125483, d159553, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro31361 (p : Pattern) (ha : d125489 p = 1) (hb : d159559 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d99 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d53648 q = 1) (hb : d125446 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d53648, d125446, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d53648, d125446, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22508 q ha hb
  have h3 (q : Pattern) (ha : d53649 q = 1) (hb : d125447 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d53649, d125447, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d53649, d125447, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d53650 q = 1) (hb : d125448 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d53650, d125448, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d53650, d125448, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d53651 q = 1) (hb : d125449 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d53651, d125449, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d53651, d125449, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d53652 q = 1) (hb : d125450 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d53652, d125450, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53652, d125450, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d125484 q = 1) (hb : d159554 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d125484, d159554, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d125484, d159554, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31360 q ha hb
  have h8 (q : Pattern) (ha : d125485 q = 1) (hb : d159555 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d125485, d159555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d125485, d159555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d125486 q = 1) (hb : d159556 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d125486, d159556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d125486, d159556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d125487 q = 1) (hb : d159557 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d125487, d159557, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d125487, d159557, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d125488 q = 1) (hb : d159558 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d125488, d159558, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d125488, d159558, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d125489 q = 1) (hb : d159559 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d125489, d159559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
    | true =>
      simp only [d125489, d159559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  exact h12 p ha hb
theorem andIntro31362 (p : Pattern) (ha : d125494 p = 1) (hb : d158723 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d14251 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d14260 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d14280 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d158718 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d125490 q = 1) (hb : d158719 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d125490, d158719, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d125490, d158719, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d14314 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d125491 q = 1) (hb : d158720 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d125491, d158720, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d125491, d158720, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d125492 q = 1) (hb : d158721 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d125492, d158721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d125492, d158721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d125493 q = 1) (hb : d158722 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d125493, d158722, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d125493, d158722, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d125494 q = 1) (hb : d158723 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d125494, d158723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d125494, d158723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro31363 (p : Pattern) (ha : d125499 p = 1) (hb : d158732 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d14251 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d14260 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d14280 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d158718 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d125490 q = 1) (hb : d158719 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d125490, d158719, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d125490, d158719, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d14314 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d125491 q = 1) (hb : d158720 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d125491, d158720, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d125491, d158720, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d125492 q = 1) (hb : d158721 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d125492, d158721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d125492, d158721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d125493 q = 1) (hb : d158722 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d125493, d158722, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d125493, d158722, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d14324 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d14329 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d14331 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d158727 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d125495 q = 1) (hb : d158728 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d125495, d158728, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
    | true =>
      simp only [d125495, d158728, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d14338 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d125496 q = 1) (hb : d158729 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d125496, d158729, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d125496, d158729, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d125497 q = 1) (hb : d158730 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d125497, d158730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
    | true =>
      simp only [d125497, d158730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d125498 q = 1) (hb : d158731 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d125498, d158731, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
    | true =>
      simp only [d125498, d158731, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d125499 q = 1) (hb : d158732 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d125499, d158732, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d125499, d158732, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro31364 (p : Pattern) (ha : d125506 p = 1) (hb : d159562 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d14331 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d158727 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d125495 q = 1) (hb : d158728 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d125495, d158728, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d125495, d158728, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d14338 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d125496 q = 1) (hb : d158729 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d125496, d158729, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d125496, d158729, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d125504 q = 1) (hb : d158730 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d125504, d158730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d125504, d158730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d125505 q = 1) (hb : d158731 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d125505, d158731, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d125505, d158731, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d125506 q = 1) (hb : d159562 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d125506, d159562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d125506, d159562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro31365 (p : Pattern) (ha : d125516 p = 1) (hb : d159573 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d14402 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d159568 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d125512 q = 1) (hb : d159569 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d125512, d159569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d125512, d159569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d14438 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d125513 q = 1) (hb : d159570 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d125513, d159570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d125513, d159570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d125514 q = 1) (hb : d159571 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d125514, d159571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d125514, d159571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d125515 q = 1) (hb : d159572 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d125515, d159572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d125515, d159572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d125516 q = 1) (hb : d159573 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d125516, d159573, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d125516, d159573, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro31366 (p : Pattern) (ha : d125522 p = 1) (hb : d159579 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d14243 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d125500 q = 1) (hb : d158733 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d125500, d158733, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31362 q ha hb
    | true =>
      simp only [d125500, d158733, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31363 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d14356 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d125501 q = 1) (hb : d158734 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d125501, d158734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d125501, d158734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d125502 q = 1) (hb : d159560 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d125502, d159560, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d125502, d159560, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d125503 q = 1) (hb : d159561 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d125503, d159561, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d125503, d159561, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d125507 q = 1) (hb : d159563 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d125507, d159563, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d125507, d159563, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31364 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d14365 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d125508 q = 1) (hb : d159564 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d125508, d159564, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d125508, d159564, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d125509 q = 1) (hb : d159565 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d125509, d159565, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d125509, d159565, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h11 (q : Pattern) (ha : d125510 q = 1) (hb : d159566 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d125510, d159566, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d125510, d159566, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h12 (q : Pattern) (ha : d125511 q = 1) (hb : d159567 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d125511, d159567, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d125511, d159567, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d125517 q = 1) (hb : d159574 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d125517, d159574, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d125517, d159574, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31365 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d14454 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d125518 q = 1) (hb : d159575 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d125518, d159575, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d125518, d159575, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d125519 q = 1) (hb : d159576 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d125519, d159576, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d125519, d159576, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h17 (q : Pattern) (ha : d125520 q = 1) (hb : d159577 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d125520, d159577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d125520, d159577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h18 (q : Pattern) (ha : d125521 q = 1) (hb : d159578 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d125521, d159578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d125521, d159578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h19 (q : Pattern) (ha : d125522 q = 1) (hb : d159579 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d125522, d159579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d125522, d159579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro31367 (p : Pattern) (ha : d125528 p = 1) (hb : d159585 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d125523 q = 1) (hb : d159580 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d125523, d159580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d125523, d159580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31366 q ha hb
  have h2 (q : Pattern) (ha : d125524 q = 1) (hb : d159581 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d125524, d159581, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d125524, d159581, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d125525 q = 1) (hb : d159582 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d125525, d159582, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d125525, d159582, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d125526 q = 1) (hb : d159583 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d125526, d159583, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d125526, d159583, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d125527 q = 1) (hb : d159584 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d125527, d159584, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d125527, d159584, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d125528 q = 1) (hb : d159585 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d125528, d159585, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d125528, d159585, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro31368 (p : Pattern) (ha : d125534 p = 1) (hb : d158866 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d14518 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d14527 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d14549 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d158861 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d125530 q = 1) (hb : d158862 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d125530, d158862, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d125530, d158862, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d14587 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d125531 q = 1) (hb : d158863 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d125531, d158863, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d125531, d158863, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d125532 q = 1) (hb : d158864 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d125532, d158864, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d125532, d158864, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d125533 q = 1) (hb : d158865 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d125533, d158865, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d125533, d158865, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d125534 q = 1) (hb : d158866 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d125534, d158866, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d125534, d158866, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro31369 (p : Pattern) (ha : d125539 p = 1) (hb : d158875 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d14518 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d14527 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d14549 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d158861 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d125530 q = 1) (hb : d158862 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d125530, d158862, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d125530, d158862, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d14587 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d125531 q = 1) (hb : d158863 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d125531, d158863, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d125531, d158863, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d125532 q = 1) (hb : d158864 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d125532, d158864, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d125532, d158864, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d125533 q = 1) (hb : d158865 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d125533, d158865, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d125533, d158865, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d14597 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d14602 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d14604 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d158870 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d125535 q = 1) (hb : d158871 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d125535, d158871, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
    | true =>
      simp only [d125535, d158871, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d14611 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d125536 q = 1) (hb : d158872 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d125536, d158872, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d125536, d158872, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d125537 q = 1) (hb : d158873 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d125537, d158873, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
    | true =>
      simp only [d125537, d158873, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d125538 q = 1) (hb : d158874 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d125538, d158874, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
    | true =>
      simp only [d125538, d158874, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d125539 q = 1) (hb : d158875 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d125539, d158875, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d125539, d158875, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro31370 (p : Pattern) (ha : d125546 p = 1) (hb : d159589 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d14604 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d158870 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d125535 q = 1) (hb : d158871 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d125535, d158871, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d125535, d158871, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d14611 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d125536 q = 1) (hb : d158872 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d125536, d158872, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d125536, d158872, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d125544 q = 1) (hb : d158873 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d125544, d158873, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d125544, d158873, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d125545 q = 1) (hb : d158874 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d125545, d158874, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d125545, d158874, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d125546 q = 1) (hb : d159589 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d125546, d159589, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d125546, d159589, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro31371 (p : Pattern) (ha : d125556 p = 1) (hb : d159600 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d14687 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d159595 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d125552 q = 1) (hb : d159596 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d125552, d159596, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d125552, d159596, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d14727 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d125553 q = 1) (hb : d159597 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d125553, d159597, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d125553, d159597, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d125554 q = 1) (hb : d159598 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d125554, d159598, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d125554, d159598, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d125555 q = 1) (hb : d159599 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d125555, d159599, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d125555, d159599, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d125556 q = 1) (hb : d159600 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d125556, d159600, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d125556, d159600, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro31372 (p : Pattern) (ha : d125562 p = 1) (hb : d159606 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d14510 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d125540 q = 1) (hb : d158876 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d125540, d158876, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31368 q ha hb
    | true =>
      simp only [d125540, d158876, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31369 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d14629 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d125541 q = 1) (hb : d158877 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d125541, d158877, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d125541, d158877, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d125542 q = 1) (hb : d159587 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d125542, d159587, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d125542, d159587, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d125543 q = 1) (hb : d159588 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d125543, d159588, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d125543, d159588, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d125547 q = 1) (hb : d159590 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d125547, d159590, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d125547, d159590, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31370 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d14638 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d125548 q = 1) (hb : d159591 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d125548, d159591, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d125548, d159591, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d125549 q = 1) (hb : d159592 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d125549, d159592, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d125549, d159592, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h11 (q : Pattern) (ha : d125550 q = 1) (hb : d159593 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d125550, d159593, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d125550, d159593, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h12 (q : Pattern) (ha : d125551 q = 1) (hb : d159594 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d125551, d159594, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d125551, d159594, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d125557 q = 1) (hb : d159601 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d125557, d159601, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d125557, d159601, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31371 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d14743 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d125558 q = 1) (hb : d159602 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d125558, d159602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d125558, d159602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d125559 q = 1) (hb : d159603 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d125559, d159603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d125559, d159603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h17 (q : Pattern) (ha : d125560 q = 1) (hb : d159604 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d125560, d159604, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d125560, d159604, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h18 (q : Pattern) (ha : d125561 q = 1) (hb : d159605 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d125561, d159605, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d125561, d159605, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h19 (q : Pattern) (ha : d125562 q = 1) (hb : d159606 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d125562, d159606, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d125562, d159606, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro31373 (p : Pattern) (ha : d125568 p = 1) (hb : d159612 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d125563 q = 1) (hb : d159607 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d125563, d159607, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d125563, d159607, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31372 q ha hb
  have h2 (q : Pattern) (ha : d125564 q = 1) (hb : d159608 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d125564, d159608, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d125564, d159608, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d125565 q = 1) (hb : d159609 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d125565, d159609, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d125565, d159609, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d125566 q = 1) (hb : d159610 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d125566, d159610, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d125566, d159610, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d125567 q = 1) (hb : d159611 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d125567, d159611, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d125567, d159611, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d125568 q = 1) (hb : d159612 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d125568, d159612, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d125568, d159612, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro31374 (p : Pattern) (ha : d125575 p = 1) (hb : d159011 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d14825 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d14834 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d14866 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d159006 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d125571 q = 1) (hb : d159007 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d125571, d159007, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d125571, d159007, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d14924 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d125572 q = 1) (hb : d159008 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d125572, d159008, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d125572, d159008, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d125573 q = 1) (hb : d159009 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d125573, d159009, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d125573, d159009, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d125574 q = 1) (hb : d159010 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d125574, d159010, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d125574, d159010, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d125575 q = 1) (hb : d159011 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d125575, d159011, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d125575, d159011, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro31375 (p : Pattern) (ha : d125580 p = 1) (hb : d159020 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d14825 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d14834 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d14866 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d159006 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d125571 q = 1) (hb : d159007 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d125571, d159007, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d125571, d159007, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d14924 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d125572 q = 1) (hb : d159008 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d125572, d159008, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d125572, d159008, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d125573 q = 1) (hb : d159009 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d125573, d159009, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d125573, d159009, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d125574 q = 1) (hb : d159010 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d125574, d159010, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d125574, d159010, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d14934 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d14939 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d14942 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d159015 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d125576 q = 1) (hb : d159016 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d125576, d159016, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
    | true =>
      simp only [d125576, d159016, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d14949 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d125577 q = 1) (hb : d159017 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d125577, d159017, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d125577, d159017, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d125578 q = 1) (hb : d159018 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d125578, d159018, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
    | true =>
      simp only [d125578, d159018, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d125579 q = 1) (hb : d159019 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d125579, d159019, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
    | true =>
      simp only [d125579, d159019, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d125580 q = 1) (hb : d159020 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d125580, d159020, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d125580, d159020, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro31376 (p : Pattern) (ha : d125587 p = 1) (hb : d159617 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d14942 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d159015 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d125576 q = 1) (hb : d159016 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d125576, d159016, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d125576, d159016, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d14949 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d125577 q = 1) (hb : d159017 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d125577, d159017, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d125577, d159017, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d125585 q = 1) (hb : d159018 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d125585, d159018, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d125585, d159018, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d125586 q = 1) (hb : d159019 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d125586, d159019, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d125586, d159019, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d125587 q = 1) (hb : d159617 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d125587, d159617, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d125587, d159617, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro31377 (p : Pattern) (ha : d125597 p = 1) (hb : d159632 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d15055 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d159627 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d125593 q = 1) (hb : d159628 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d125593, d159628, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d125593, d159628, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d15119 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d125594 q = 1) (hb : d159629 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d125594, d159629, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d125594, d159629, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d125595 q = 1) (hb : d159630 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d125595, d159630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d125595, d159630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d125596 q = 1) (hb : d159631 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d125596, d159631, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d125596, d159631, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d125597 q = 1) (hb : d159632 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d125597, d159632, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d125597, d159632, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro31378 (p : Pattern) (ha : d125603 p = 1) (hb : d159638 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d14817 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d125581 q = 1) (hb : d159021 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d125581, d159021, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31374 q ha hb
    | true =>
      simp only [d125581, d159021, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31375 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d14972 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d125582 q = 1) (hb : d159022 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d125582, d159022, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d125582, d159022, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d125583 q = 1) (hb : d159615 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d125583, d159615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d125583, d159615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d125584 q = 1) (hb : d159616 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d125584, d159616, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d125584, d159616, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d125588 q = 1) (hb : d159618 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d125588, d159618, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d125588, d159618, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31376 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d14981 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d125589 q = 1) (hb : d159619 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d125589, d159619, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d125589, d159619, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d125590 q = 1) (hb : d159620 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d125590, d159620, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d125590, d159620, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h11 (q : Pattern) (ha : d125591 q = 1) (hb : d159621 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d125591, d159621, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d125591, d159621, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h12 (q : Pattern) (ha : d125592 q = 1) (hb : d159622 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d125592, d159622, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d125592, d159622, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d125598 q = 1) (hb : d159633 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d125598, d159633, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d125598, d159633, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31377 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d15135 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d125599 q = 1) (hb : d159634 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d125599, d159634, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d125599, d159634, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d125600 q = 1) (hb : d159635 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d125600, d159635, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d125600, d159635, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h17 (q : Pattern) (ha : d125601 q = 1) (hb : d159636 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d125601, d159636, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d125601, d159636, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h18 (q : Pattern) (ha : d125602 q = 1) (hb : d159637 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d125602, d159637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d125602, d159637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h19 (q : Pattern) (ha : d125603 q = 1) (hb : d159638 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d125603, d159638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d125603, d159638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro31379 (p : Pattern) (ha : d125609 p = 1) (hb : d159644 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d125604 q = 1) (hb : d159639 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d125604, d159639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d125604, d159639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31378 q ha hb
  have h2 (q : Pattern) (ha : d125605 q = 1) (hb : d159640 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d125605, d159640, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d125605, d159640, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d125606 q = 1) (hb : d159641 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d125606, d159641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d125606, d159641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d125607 q = 1) (hb : d159642 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d125607, d159642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d125607, d159642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d125608 q = 1) (hb : d159643 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d125608, d159643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d125608, d159643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d125609 q = 1) (hb : d159644 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d125609, d159644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d125609, d159644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro31380 (p : Pattern) (ha : d125617 p = 1) (hb : d159175 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d15218 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d15227 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d15259 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d159170 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d125613 q = 1) (hb : d159171 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d125613, d159171, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d125613, d159171, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d15317 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d125614 q = 1) (hb : d159172 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d125614, d159172, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d125614, d159172, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d125615 q = 1) (hb : d159173 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d125615, d159173, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d125615, d159173, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d125616 q = 1) (hb : d159174 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d125616, d159174, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d125616, d159174, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d125617 q = 1) (hb : d159175 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d125617, d159175, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d125617, d159175, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro31381 (p : Pattern) (ha : d125622 p = 1) (hb : d159184 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d15218 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d15227 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d15259 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d159170 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d125613 q = 1) (hb : d159171 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d125613, d159171, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d125613, d159171, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d15317 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d125614 q = 1) (hb : d159172 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d125614, d159172, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d125614, d159172, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d125615 q = 1) (hb : d159173 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d125615, d159173, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d125615, d159173, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d125616 q = 1) (hb : d159174 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d125616, d159174, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d125616, d159174, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d15327 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d15332 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d15335 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d159179 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d125618 q = 1) (hb : d159180 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d125618, d159180, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
    | true =>
      simp only [d125618, d159180, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d15342 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d125619 q = 1) (hb : d159181 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d125619, d159181, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d125619, d159181, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d125620 q = 1) (hb : d159182 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d125620, d159182, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
    | true =>
      simp only [d125620, d159182, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d125621 q = 1) (hb : d159183 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d125621, d159183, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
    | true =>
      simp only [d125621, d159183, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d125622 q = 1) (hb : d159184 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d125622, d159184, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d125622, d159184, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro31382 (p : Pattern) (ha : d125629 p = 1) (hb : d159650 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d15335 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d159179 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d125618 q = 1) (hb : d159180 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d125618, d159180, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d125618, d159180, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d15342 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d125619 q = 1) (hb : d159181 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d125619, d159181, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d125619, d159181, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d125627 q = 1) (hb : d159182 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d125627, d159182, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d125627, d159182, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d125628 q = 1) (hb : d159183 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d125628, d159183, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d125628, d159183, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d125629 q = 1) (hb : d159650 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d125629, d159650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d125629, d159650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro31383 (p : Pattern) (ha : d125639 p = 1) (hb : d159665 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d15448 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d159660 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d125635 q = 1) (hb : d159661 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d125635, d159661, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d125635, d159661, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d15512 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d125636 q = 1) (hb : d159662 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d125636, d159662, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d125636, d159662, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d125637 q = 1) (hb : d159663 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d125637, d159663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d125637, d159663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d125638 q = 1) (hb : d159664 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d125638, d159664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d125638, d159664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d125639 q = 1) (hb : d159665 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d125639, d159665, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d125639, d159665, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro31384 (p : Pattern) (ha : d125645 p = 1) (hb : d159671 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d15210 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d125623 q = 1) (hb : d159185 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d125623, d159185, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31380 q ha hb
    | true =>
      simp only [d125623, d159185, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31381 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d15365 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d125624 q = 1) (hb : d159186 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d125624, d159186, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d125624, d159186, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d125625 q = 1) (hb : d159648 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d125625, d159648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d125625, d159648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d125626 q = 1) (hb : d159649 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d125626, d159649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d125626, d159649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d125630 q = 1) (hb : d159651 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d125630, d159651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d125630, d159651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31382 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d15374 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d125631 q = 1) (hb : d159652 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d125631, d159652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d125631, d159652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d125632 q = 1) (hb : d159653 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d125632, d159653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d125632, d159653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h11 (q : Pattern) (ha : d125633 q = 1) (hb : d159654 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d125633, d159654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d125633, d159654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h12 (q : Pattern) (ha : d125634 q = 1) (hb : d159655 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d125634, d159655, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d125634, d159655, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d125640 q = 1) (hb : d159666 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d125640, d159666, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d125640, d159666, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31383 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d15528 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d125641 q = 1) (hb : d159667 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d125641, d159667, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d125641, d159667, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d125642 q = 1) (hb : d159668 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d125642, d159668, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d125642, d159668, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h17 (q : Pattern) (ha : d125643 q = 1) (hb : d159669 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d125643, d159669, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d125643, d159669, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h18 (q : Pattern) (ha : d125644 q = 1) (hb : d159670 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d125644, d159670, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d125644, d159670, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h19 (q : Pattern) (ha : d125645 q = 1) (hb : d159671 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d125645, d159671, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d125645, d159671, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro31385 (p : Pattern) (ha : d125651 p = 1) (hb : d159677 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d125646 q = 1) (hb : d159672 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d125646, d159672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d125646, d159672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31384 q ha hb
  have h2 (q : Pattern) (ha : d125647 q = 1) (hb : d159673 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d125647, d159673, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d125647, d159673, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d125648 q = 1) (hb : d159674 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d125648, d159674, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d125648, d159674, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d125649 q = 1) (hb : d159675 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d125649, d159675, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d125649, d159675, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d125650 q = 1) (hb : d159676 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d125650, d159676, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d125650, d159676, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d125651 q = 1) (hb : d159677 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d125651, d159677, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d125651, d159677, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro31386 (p : Pattern) (ha : d125660 p = 1) (hb : d159340 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d15610 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d15619 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d15647 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d159335 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d125656 q = 1) (hb : d159336 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d125656, d159336, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d125656, d159336, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d15705 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d125657 q = 1) (hb : d159337 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d125657, d159337, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d125657, d159337, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d125658 q = 1) (hb : d159338 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d125658, d159338, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d125658, d159338, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d125659 q = 1) (hb : d159339 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d125659, d159339, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d125659, d159339, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d125660 q = 1) (hb : d159340 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d125660, d159340, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d125660, d159340, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro31387 (p : Pattern) (ha : d125665 p = 1) (hb : d159349 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d15610 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d15619 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d15647 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d159335 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d125656 q = 1) (hb : d159336 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d125656, d159336, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d125656, d159336, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d15705 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d125657 q = 1) (hb : d159337 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d125657, d159337, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d125657, d159337, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d125658 q = 1) (hb : d159338 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d125658, d159338, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d125658, d159338, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d125659 q = 1) (hb : d159339 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d125659, d159339, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d125659, d159339, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d15715 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d15720 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d15723 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d159344 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d125661 q = 1) (hb : d159345 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d125661, d159345, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
    | true =>
      simp only [d125661, d159345, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d15730 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d125662 q = 1) (hb : d159346 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d125662, d159346, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d125662, d159346, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d125663 q = 1) (hb : d159347 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d125663, d159347, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
    | true =>
      simp only [d125663, d159347, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d125664 q = 1) (hb : d159348 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d125664, d159348, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
    | true =>
      simp only [d125664, d159348, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d125665 q = 1) (hb : d159349 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d125665, d159349, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d125665, d159349, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro31388 (p : Pattern) (ha : d125672 p = 1) (hb : d159684 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d15723 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d159344 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d125661 q = 1) (hb : d159345 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d125661, d159345, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d125661, d159345, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d15730 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d125662 q = 1) (hb : d159346 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d125662, d159346, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d125662, d159346, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d125670 q = 1) (hb : d159347 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d125670, d159347, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d125670, d159347, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d125671 q = 1) (hb : d159348 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d125671, d159348, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d125671, d159348, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d125672 q = 1) (hb : d159684 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d125672, d159684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d125672, d159684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro31389 (p : Pattern) (ha : d125682 p = 1) (hb : d159699 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d15826 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d159694 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d125678 q = 1) (hb : d159695 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d125678, d159695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d125678, d159695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d15890 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d125679 q = 1) (hb : d159696 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d125679, d159696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d125679, d159696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d125680 q = 1) (hb : d159697 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d125680, d159697, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d125680, d159697, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d125681 q = 1) (hb : d159698 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d125681, d159698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d125681, d159698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d125682 q = 1) (hb : d159699 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d125682, d159699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d125682, d159699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro31390 (p : Pattern) (ha : d125688 p = 1) (hb : d159705 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d15602 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d125666 q = 1) (hb : d159350 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d125666, d159350, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31386 q ha hb
    | true =>
      simp only [d125666, d159350, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31387 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d15753 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d125667 q = 1) (hb : d159351 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d125667, d159351, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d125667, d159351, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d125668 q = 1) (hb : d159682 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d125668, d159682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d125668, d159682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d125669 q = 1) (hb : d159683 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d125669, d159683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d125669, d159683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d125673 q = 1) (hb : d159685 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d125673, d159685, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d125673, d159685, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31388 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d15762 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d125674 q = 1) (hb : d159686 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d125674, d159686, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d125674, d159686, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d125675 q = 1) (hb : d159687 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d125675, d159687, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d125675, d159687, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h11 (q : Pattern) (ha : d125676 q = 1) (hb : d159688 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d125676, d159688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d125676, d159688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h12 (q : Pattern) (ha : d125677 q = 1) (hb : d159689 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d125677, d159689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d125677, d159689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d125683 q = 1) (hb : d159700 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d125683, d159700, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d125683, d159700, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31389 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d15906 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d125684 q = 1) (hb : d159701 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d125684, d159701, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d125684, d159701, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d125685 q = 1) (hb : d159702 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d125685, d159702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d125685, d159702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h17 (q : Pattern) (ha : d125686 q = 1) (hb : d159703 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d125686, d159703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d125686, d159703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h18 (q : Pattern) (ha : d125687 q = 1) (hb : d159704 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d125687, d159704, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d125687, d159704, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h19 (q : Pattern) (ha : d125688 q = 1) (hb : d159705 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d125688, d159705, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d125688, d159705, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro31391 (p : Pattern) (ha : d125694 p = 1) (hb : d159711 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d125689 q = 1) (hb : d159706 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d125689, d159706, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d125689, d159706, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31390 q ha hb
  have h2 (q : Pattern) (ha : d125690 q = 1) (hb : d159707 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d125690, d159707, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d125690, d159707, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d125691 q = 1) (hb : d159708 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d125691, d159708, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d125691, d159708, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d125692 q = 1) (hb : d159709 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d125692, d159709, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d125692, d159709, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d125693 q = 1) (hb : d159710 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d125693, d159710, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d125693, d159710, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d125694 q = 1) (hb : d159711 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d125694, d159711, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d125694, d159711, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro31392 (p : Pattern) (ha : d125700 p = 1) (hb : d159717 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d125529 q = 1) (hb : d159586 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d125529, d159586, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31361 q ha hb
    | true =>
      simp only [d125529, d159586, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31367 q ha hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d125569 q = 1) (hb : d159613 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d125569, d159613, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d125569, d159613, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31373 q ha hb
  have h3 (q : Pattern) (ha : d125570 q = 1) (hb : d159614 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d125570, d159614, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d125570, d159614, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d125610 q = 1) (hb : d159645 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d125610, d159645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d125610, d159645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31379 q ha hb
  have h5 (q : Pattern) (ha : d125611 q = 1) (hb : d159646 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d125611, d159646, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d125611, d159646, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d125612 q = 1) (hb : d159647 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d125612, d159647, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d125612, d159647, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d125652 q = 1) (hb : d159678 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d125652, d159678, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d125652, d159678, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31385 q ha hb
  have h8 (q : Pattern) (ha : d125653 q = 1) (hb : d159679 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d125653, d159679, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d125653, d159679, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d125654 q = 1) (hb : d159680 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d125654, d159680, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d125654, d159680, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d125655 q = 1) (hb : d159681 q = 1) : d0 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d125655, d159681, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d125655, d159681, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d125695 q = 1) (hb : d159712 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d125695, d159712, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d125695, d159712, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31391 q ha hb
  have h12 (q : Pattern) (ha : d125696 q = 1) (hb : d159713 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d125696, d159713, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d125696, d159713, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d125697 q = 1) (hb : d159714 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d125697, d159714, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d125697, d159714, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d125698 q = 1) (hb : d159715 q = 1) : d0 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d125698, d159715, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d125698, d159715, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d125699 q = 1) (hb : d159716 q = 1) : d0 q = 1 := by
    cases bit : q 10250 with
    | false =>
      simp only [d125699, d159716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d125699, d159716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d125700 q = 1) (hb : d159717 q = 1) : d0 q = 1 := by
    cases bit : q 260 with
    | false =>
      simp only [d125700, d159717, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d125700, d159717, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  exact h16 p ha hb
theorem andIntro31393 (p : Pattern) (ha : d125706 p = 1) (hb : d159723 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d125701 q = 1) (hb : d159718 q = 1) : d0 q = 1 := by
    cases bit : q 259 with
    | false =>
      simp only [d125701, d159718, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31392 q ha hb
    | true =>
      simp only [d125701, d159718, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d125702 q = 1) (hb : d159719 q = 1) : d0 q = 1 := by
    cases bit : q 258 with
    | false =>
      simp only [d125702, d159719, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d125702, d159719, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d125703 q = 1) (hb : d159720 q = 1) : d0 q = 1 := by
    cases bit : q 257 with
    | false =>
      simp only [d125703, d159720, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d125703, d159720, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d125704 q = 1) (hb : d159721 q = 1) : d0 q = 1 := by
    cases bit : q 256 with
    | false =>
      simp only [d125704, d159721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d125704, d159721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d125705 q = 1) (hb : d159722 q = 1) : d0 q = 1 := by
    cases bit : q 255 with
    | false =>
      simp only [d125705, d159722, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d125705, d159722, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d125706 q = 1) (hb : d159723 q = 1) : d0 q = 1 := by
    cases bit : q 254 with
    | false =>
      simp only [d125706, d159723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d125706, d159723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro31394 (p : Pattern) (ha : d125712 p = 1) (hb : d159729 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d125707 q = 1) (hb : d159724 q = 1) : d0 q = 1 := by
    cases bit : q 253 with
    | false =>
      simp only [d125707, d159724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31393 q ha hb
    | true =>
      simp only [d125707, d159724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d125708 q = 1) (hb : d159725 q = 1) : d0 q = 1 := by
    cases bit : q 252 with
    | false =>
      simp only [d125708, d159725, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d125708, d159725, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d125709 q = 1) (hb : d159726 q = 1) : d0 q = 1 := by
    cases bit : q 251 with
    | false =>
      simp only [d125709, d159726, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d125709, d159726, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d125710 q = 1) (hb : d159727 q = 1) : d0 q = 1 := by
    cases bit : q 250 with
    | false =>
      simp only [d125710, d159727, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d125710, d159727, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d125711 q = 1) (hb : d159728 q = 1) : d0 q = 1 := by
    cases bit : q 249 with
    | false =>
      simp only [d125711, d159728, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d125711, d159728, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d125712 q = 1) (hb : d159729 q = 1) : d0 q = 1 := by
    cases bit : q 245 with
    | false =>
      simp only [d125712, d159729, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d125712, d159729, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro31395 (p : Pattern) (ha : d125718 p = 1) (hb : d159735 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d125713 q = 1) (hb : d159730 q = 1) : d0 q = 1 := by
    cases bit : q 200 with
    | false =>
      simp only [d125713, d159730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31394 q ha hb
    | true =>
      simp only [d125713, d159730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d125714 q = 1) (hb : d159731 q = 1) : d0 q = 1 := by
    cases bit : q 199 with
    | false =>
      simp only [d125714, d159731, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d125714, d159731, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d125715 q = 1) (hb : d159732 q = 1) : d0 q = 1 := by
    cases bit : q 186 with
    | false =>
      simp only [d125715, d159732, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d125715, d159732, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d125716 q = 1) (hb : d159733 q = 1) : d0 q = 1 := by
    cases bit : q 185 with
    | false =>
      simp only [d125716, d159733, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d125716, d159733, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d125717 q = 1) (hb : d159734 q = 1) : d0 q = 1 := by
    cases bit : q 184 with
    | false =>
      simp only [d125717, d159734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d125717, d159734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d125718 q = 1) (hb : d159735 q = 1) : d0 q = 1 := by
    cases bit : q 181 with
    | false =>
      simp only [d125718, d159735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d125718, d159735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro31396 (p : Pattern) (ha : d125724 p = 1) (hb : d159741 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d125719 q = 1) (hb : d159736 q = 1) : d0 q = 1 := by
    cases bit : q 177 with
    | false =>
      simp only [d125719, d159736, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31395 q ha hb
    | true =>
      simp only [d125719, d159736, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d125720 q = 1) (hb : d159737 q = 1) : d0 q = 1 := by
    cases bit : q 164 with
    | false =>
      simp only [d125720, d159737, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d125720, d159737, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d125721 q = 1) (hb : d159738 q = 1) : d0 q = 1 := by
    cases bit : q 156 with
    | false =>
      simp only [d125721, d159738, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d125721, d159738, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d125722 q = 1) (hb : d159739 q = 1) : d0 q = 1 := by
    cases bit : q 155 with
    | false =>
      simp only [d125722, d159739, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d125722, d159739, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d125723 q = 1) (hb : d159740 q = 1) : d0 q = 1 := by
    cases bit : q 134 with
    | false =>
      simp only [d125723, d159740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d125723, d159740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d125724 q = 1) (hb : d159741 q = 1) : d0 q = 1 := by
    cases bit : q 133 with
    | false =>
      simp only [d125724, d159741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d125724, d159741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro31397 (p : Pattern) (ha : d125730 p = 1) (hb : d159747 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d125725 q = 1) (hb : d159742 q = 1) : d0 q = 1 := by
    cases bit : q 120 with
    | false =>
      simp only [d125725, d159742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31396 q ha hb
    | true =>
      simp only [d125725, d159742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d125726 q = 1) (hb : d159743 q = 1) : d0 q = 1 := by
    cases bit : q 118 with
    | false =>
      simp only [d125726, d159743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d125726, d159743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d125727 q = 1) (hb : d159744 q = 1) : d0 q = 1 := by
    cases bit : q 114 with
    | false =>
      simp only [d125727, d159744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d125727, d159744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d125728 q = 1) (hb : d159745 q = 1) : d0 q = 1 := by
    cases bit : q 111 with
    | false =>
      simp only [d125728, d159745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d125728, d159745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d125729 q = 1) (hb : d159746 q = 1) : d0 q = 1 := by
    cases bit : q 98 with
    | false =>
      simp only [d125729, d159746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d125729, d159746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d125730 q = 1) (hb : d159747 q = 1) : d0 q = 1 := by
    cases bit : q 97 with
    | false =>
      simp only [d125730, d159747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d125730, d159747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro31398 (p : Pattern) (ha : d125736 p = 1) (hb : d159753 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d125731 q = 1) (hb : d159748 q = 1) : d0 q = 1 := by
    cases bit : q 94 with
    | false =>
      simp only [d125731, d159748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31397 q ha hb
    | true =>
      simp only [d125731, d159748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d125732 q = 1) (hb : d159749 q = 1) : d0 q = 1 := by
    cases bit : q 76 with
    | false =>
      simp only [d125732, d159749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d125732, d159749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d125733 q = 1) (hb : d159750 q = 1) : d0 q = 1 := by
    cases bit : q 67 with
    | false =>
      simp only [d125733, d159750, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d125733, d159750, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d125734 q = 1) (hb : d159751 q = 1) : d0 q = 1 := by
    cases bit : q 52 with
    | false =>
      simp only [d125734, d159751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d125734, d159751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d125735 q = 1) (hb : d159752 q = 1) : d0 q = 1 := by
    cases bit : q 47 with
    | false =>
      simp only [d125735, d159752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d125735, d159752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d125736 q = 1) (hb : d159753 q = 1) : d0 q = 1 := by
    cases bit : q 46 with
    | false =>
      simp only [d125736, d159753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d125736, d159753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro31399 (p : Pattern) (ha : d125742 p = 1) (hb : d159759 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d125737 q = 1) (hb : d159754 q = 1) : d0 q = 1 := by
    cases bit : q 45 with
    | false =>
      simp only [d125737, d159754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31398 q ha hb
    | true =>
      simp only [d125737, d159754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d125738 q = 1) (hb : d159755 q = 1) : d0 q = 1 := by
    cases bit : q 30 with
    | false =>
      simp only [d125738, d159755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d125738, d159755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d125739 q = 1) (hb : d159756 q = 1) : d0 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d125739, d159756, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d125739, d159756, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d125740 q = 1) (hb : d159757 q = 1) : d0 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d125740, d159757, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d125740, d159757, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d125741 q = 1) (hb : d159758 q = 1) : d0 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d125741, d159758, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d125741, d159758, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d125742 q = 1) (hb : d159759 q = 1) : d0 q = 1 := by
    cases bit : q 25 with
    | false =>
      simp only [d125742, d159759, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d125742, d159759, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro31400 (p : Pattern) (ha : d30 p = 1) (hb : d159762 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d28 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d100904 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d29 q = 1) (hb : d159761 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d29, d159761, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d29, d159761, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d30 q = 1) (hb : d159762 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d30, d159762, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d30, d159762, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  exact h4 p ha hb
theorem andIntro31401 (p : Pattern) (ha : d36 p = 1) (hb : d159762 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d159762 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d31 q = 1) (hb : d159762 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d31, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31400 q ha hb
    | true =>
      simp only [d31, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d32 q = 1) (hb : d159762 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d32, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d32, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d33 q = 1) (hb : d159762 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d33, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d33, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d34 q = 1) (hb : d159762 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d34, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d34, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d35 q = 1) (hb : d159762 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d35, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d35, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d36 q = 1) (hb : d159762 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d36, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d36, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro31402 (p : Pattern) (ha : d42 p = 1) (hb : d159762 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d159762 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d37 q = 1) (hb : d159762 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d37, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31401 q ha hb
    | true =>
      simp only [d37, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d38 q = 1) (hb : d159762 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d38, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d38, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d39 q = 1) (hb : d159762 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d39, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d39, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d40 q = 1) (hb : d159762 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d40, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d40, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d41 q = 1) (hb : d159762 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d41, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d41, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d42 q = 1) (hb : d159762 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d42, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d42, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro31403 (p : Pattern) (ha : d48 p = 1) (hb : d159762 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d159762 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d43 q = 1) (hb : d159762 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d43, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31402 q ha hb
    | true =>
      simp only [d43, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d44 q = 1) (hb : d159762 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d44, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d44, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d45 q = 1) (hb : d159762 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d45, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d45, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d46 q = 1) (hb : d159762 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d46, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d46, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d47 q = 1) (hb : d159762 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d47, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d47, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d48 q = 1) (hb : d159762 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d48, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d48, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro31404 (p : Pattern) (ha : d49 p = 1) (hb : d159762 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d159762 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d37 q = 1) (hb : d159762 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d37, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31401 q ha hb
    | true =>
      simp only [d37, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d38 q = 1) (hb : d159762 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d38, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d38, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d39 q = 1) (hb : d159762 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d39, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d39, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d40 q = 1) (hb : d159762 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d40, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d40, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d41 q = 1) (hb : d159762 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d41, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d41, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d49 q = 1) (hb : d159762 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d49, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d49, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro31405 (p : Pattern) (ha : d55 p = 1) (hb : d159762 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d159762 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d43 q = 1) (hb : d159762 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d43, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31402 q ha hb
    | true =>
      simp only [d43, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d44 q = 1) (hb : d159762 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d44, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d44, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d45 q = 1) (hb : d159762 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d45, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d45, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d46 q = 1) (hb : d159762 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d46, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d46, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d47 q = 1) (hb : d159762 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d47, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d47, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d50 q = 1) (hb : d159762 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d50, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31404 q ha hb
    | true =>
      simp only [d50, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d51 q = 1) (hb : d159762 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d51, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d51, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d52 q = 1) (hb : d159762 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d52, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d52, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d53 q = 1) (hb : d159762 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d53, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d54 q = 1) (hb : d159762 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d54, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d55 q = 1) (hb : d159762 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d55, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d55, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro31406 (p : Pattern) (ha : d60 p = 1) (hb : d159762 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d159762 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d50 q = 1) (hb : d159762 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d50, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31404 q ha hb
    | true =>
      simp only [d50, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d51 q = 1) (hb : d159762 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d51, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d51, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d52 q = 1) (hb : d159762 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d52, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d52, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d53 q = 1) (hb : d159762 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d53, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d54 q = 1) (hb : d159762 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d54, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d60 q = 1) (hb : d159762 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d60, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d60, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro31407 (p : Pattern) (ha : d71 p = 1) (hb : d159762 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d69 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d100904 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d70 q = 1) (hb : d159761 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d70, d159761, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d70, d159761, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d71 q = 1) (hb : d159762 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d71, d159762, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d71, d159762, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  exact h4 p ha hb
theorem andIntro31408 (p : Pattern) (ha : d77 p = 1) (hb : d159762 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d159762 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d72 q = 1) (hb : d159762 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d72, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31407 q ha hb
    | true =>
      simp only [d72, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d73 q = 1) (hb : d159762 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d73, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d73, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d74 q = 1) (hb : d159762 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d74, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d74, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d75 q = 1) (hb : d159762 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d75, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d75, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d76 q = 1) (hb : d159762 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d76, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d76, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d77 q = 1) (hb : d159762 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d77, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d77, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro31409 (p : Pattern) (ha : d83 p = 1) (hb : d159762 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d159762 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d78 q = 1) (hb : d159762 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d78, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31408 q ha hb
    | true =>
      simp only [d78, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d79 q = 1) (hb : d159762 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d79, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d79, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d80 q = 1) (hb : d159762 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d80, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d80, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d81 q = 1) (hb : d159762 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d81, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d81, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d82 q = 1) (hb : d159762 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d82, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d82, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d83 q = 1) (hb : d159762 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d83, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d83, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro31410 (p : Pattern) (ha : d89 p = 1) (hb : d159762 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d159762 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d84 q = 1) (hb : d159762 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d84, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31409 q ha hb
    | true =>
      simp only [d84, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d85 q = 1) (hb : d159762 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d85, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d85, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d86 q = 1) (hb : d159762 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d86, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d86, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d87 q = 1) (hb : d159762 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d87, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d87, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d88 q = 1) (hb : d159762 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d88, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d88, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d89 q = 1) (hb : d159762 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d89, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d89, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro31411 (p : Pattern) (ha : d95 p = 1) (hb : d159762 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d159762 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d56 q = 1) (hb : d159762 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d56, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31403 q ha hb
    | true =>
      simp only [d56, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31405 q ha hb
  have h2 (q : Pattern) (ha : d57 q = 1) (hb : d159762 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d57, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d57, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d58 q = 1) (hb : d159762 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d58, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d58, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d59 q = 1) (hb : d159762 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d59, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d59, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d61 q = 1) (hb : d159762 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d61, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d61, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31406 q ha hb
  have h6 (q : Pattern) (ha : d62 q = 1) (hb : d159762 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d62, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d62, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d63 q = 1) (hb : d159762 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d63, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d63, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d64 q = 1) (hb : d159762 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d64, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d64, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d65 q = 1) (hb : d159762 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d65, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d65, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d90 q = 1) (hb : d159762 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d90, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d90, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31410 q ha hb
  have h11 (q : Pattern) (ha : d91 q = 1) (hb : d159762 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d91, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d91, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d92 q = 1) (hb : d159762 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d92, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d92, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d93 q = 1) (hb : d159762 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d93, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d93, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d94 q = 1) (hb : d159762 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d94, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d94, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d95 q = 1) (hb : d159762 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d95, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d95, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro31412 (p : Pattern) (ha : d104 p = 1) (hb : d159762 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d159762 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d43 q = 1) (hb : d159762 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d43, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31402 q ha hb
    | true =>
      simp only [d43, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d100 q = 1) (hb : d159762 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d100, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d100, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d101 q = 1) (hb : d159762 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d101, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d101, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d102 q = 1) (hb : d159762 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d103 q = 1) (hb : d159762 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d104 q = 1) (hb : d159762 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d104, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d104, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro31413 (p : Pattern) (ha : d111 p = 1) (hb : d159762 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d159762 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d43 q = 1) (hb : d159762 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d43, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31402 q ha hb
    | true =>
      simp only [d43, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d100 q = 1) (hb : d159762 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d100, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d100, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d101 q = 1) (hb : d159762 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d101, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d101, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d102 q = 1) (hb : d159762 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d103 q = 1) (hb : d159762 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d50 q = 1) (hb : d159762 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d50, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31404 q ha hb
    | true =>
      simp only [d50, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d107 q = 1) (hb : d159762 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d107, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d107, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d108 q = 1) (hb : d159762 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d108, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d108, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d109 q = 1) (hb : d159762 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d109, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d109, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d110 q = 1) (hb : d159762 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d110, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d110, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d111 q = 1) (hb : d159762 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d111, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d111, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro31414 (p : Pattern) (ha : d213 p = 1) (hb : d159762 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d159762 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d43 q = 1) (hb : d159762 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d43, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31402 q ha hb
    | true =>
      simp only [d43, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d100 q = 1) (hb : d159762 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d100, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d100, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d101 q = 1) (hb : d159762 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d101, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d101, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d102 q = 1) (hb : d159762 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d103 q = 1) (hb : d159762 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d213 q = 1) (hb : d159762 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d213, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d213, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro31415 (p : Pattern) (ha : d116 p = 1) (hb : d159762 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d159762 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d37 q = 1) (hb : d159762 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d37, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31401 q ha hb
    | true =>
      simp only [d37, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d38 q = 1) (hb : d159762 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d38, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d38, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d39 q = 1) (hb : d159762 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d39, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d39, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d40 q = 1) (hb : d159762 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d40, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d40, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d115 q = 1) (hb : d159762 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d115, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d115, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d116 q = 1) (hb : d159762 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d116, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d116, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro31416 (p : Pattern) (ha : d123 p = 1) (hb : d159762 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d159762 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d37 q = 1) (hb : d159762 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d37, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31401 q ha hb
    | true =>
      simp only [d37, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d38 q = 1) (hb : d159762 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d38, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d38, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d39 q = 1) (hb : d159762 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d39, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d39, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d121 q = 1) (hb : d159762 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d122 q = 1) (hb : d159762 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d123 q = 1) (hb : d159762 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d123, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d123, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro31417 (p : Pattern) (ha : d4818 p = 1) (hb : d159762 p = 1) : d159797 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d142 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d28 q = 1) (hb : d100904 q = 1) : d28 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d143 q = 1) (hb : d159761 q = 1) : d159796 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d143, d159761, d159796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d143, d159761, d159796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d4818 q = 1) (hb : d159762 q = 1) : d159797 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d4818, d159762, d159797, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d4818, d159762, d159797, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  exact h4 p ha hb
theorem andIntro31418 (p : Pattern) (ha : d12227 p = 1) (hb : d159762 p = 1) : d159803 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d159762 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d4819 q = 1) (hb : d159762 q = 1) : d159798 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d4819, d159798, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31417 q ha hb
    | true =>
      simp only [d4819, d159798, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31400 q ha hb
  have h2 (q : Pattern) (ha : d4820 q = 1) (hb : d159762 q = 1) : d159799 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d4820, d159799, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4820, d159799, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d4821 q = 1) (hb : d159762 q = 1) : d159800 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d4821, d159800, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4821, d159800, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d31 q = 1) (hb : d159762 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d31, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31400 q ha hb
    | true =>
      simp only [d31, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d32 q = 1) (hb : d159762 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d32, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d32, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d33 q = 1) (hb : d159762 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d33, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d33, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d12225 q = 1) (hb : d159762 q = 1) : d159801 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d12225, d159801, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d12225, d159801, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d34 q = 1) (hb : d159762 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d34, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d34, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d12226 q = 1) (hb : d159762 q = 1) : d159802 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d12226, d159802, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d12226, d159802, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d12227 q = 1) (hb : d159762 q = 1) : d159803 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d12227, d159803, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d12227, d159803, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h10 p ha hb
theorem andIntro31419 (p : Pattern) (ha : d12233 p = 1) (hb : d159762 p = 1) : d159809 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d159762 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12228 q = 1) (hb : d159762 q = 1) : d159804 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d12228, d159804, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31418 q ha hb
    | true =>
      simp only [d12228, d159804, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d12229 q = 1) (hb : d159762 q = 1) : d159805 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d12229, d159805, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12229, d159805, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d37 q = 1) (hb : d159762 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d37, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31401 q ha hb
    | true =>
      simp only [d37, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d38 q = 1) (hb : d159762 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d38, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d38, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d12230 q = 1) (hb : d159762 q = 1) : d159806 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d12230, d159806, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d12230, d159806, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d12231 q = 1) (hb : d159762 q = 1) : d159807 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d12231, d159807, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d12231, d159807, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d12232 q = 1) (hb : d159762 q = 1) : d159808 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d12232, d159808, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d12232, d159808, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d12233 q = 1) (hb : d159762 q = 1) : d159809 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d12233, d159809, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12233, d159809, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro31420 (p : Pattern) (ha : d115242 p = 1) (hb : d159762 p = 1) : d159815 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d159762 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d117 q = 1) (hb : d159762 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d117, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31415 q ha hb
    | true =>
      simp only [d117, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d118 q = 1) (hb : d159762 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d119 q = 1) (hb : d159762 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d120 q = 1) (hb : d159762 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d124 q = 1) (hb : d159762 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31416 q ha hb
    | true =>
      simp only [d124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d125 q = 1) (hb : d159762 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d126 q = 1) (hb : d159762 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d12234 q = 1) (hb : d159762 q = 1) : d159810 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d12234, d159810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31419 q ha hb
    | true =>
      simp only [d12234, d159810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31402 q ha hb
  have h9 (q : Pattern) (ha : d115238 q = 1) (hb : d159762 q = 1) : d159811 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d115238, d159811, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d115238, d159811, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d43 q = 1) (hb : d159762 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d43, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31402 q ha hb
    | true =>
      simp only [d43, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d44 q = 1) (hb : d159762 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d44, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d44, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d115239 q = 1) (hb : d159762 q = 1) : d159812 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d115239, d159812, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d115239, d159812, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d115240 q = 1) (hb : d159762 q = 1) : d159813 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d115240, d159813, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d115240, d159813, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d115241 q = 1) (hb : d159762 q = 1) : d159814 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d115241, d159814, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d115241, d159814, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d115242 q = 1) (hb : d159762 q = 1) : d159815 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d115242, d159815, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d115242, d159815, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro31421 (p : Pattern) (ha : d194 p = 1) (hb : d159762 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d159762 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d37 q = 1) (hb : d159762 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d37, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31401 q ha hb
    | true =>
      simp only [d37, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d38 q = 1) (hb : d159762 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d38, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d38, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d39 q = 1) (hb : d159762 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d39, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d39, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d40 q = 1) (hb : d159762 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d40, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d40, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d115 q = 1) (hb : d159762 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d115, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d115, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d194 q = 1) (hb : d159762 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d194, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d194, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro31422 (p : Pattern) (ha : d199 p = 1) (hb : d159762 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d159762 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d37 q = 1) (hb : d159762 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d37, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31401 q ha hb
    | true =>
      simp only [d37, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d38 q = 1) (hb : d159762 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d38, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d38, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d39 q = 1) (hb : d159762 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d39, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d39, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d121 q = 1) (hb : d159762 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d122 q = 1) (hb : d159762 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d199 q = 1) (hb : d159762 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d199, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d199, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro31423 (p : Pattern) (ha : d12240 p = 1) (hb : d159762 p = 1) : d159816 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d159762 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12228 q = 1) (hb : d159762 q = 1) : d159804 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d12228, d159804, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31418 q ha hb
    | true =>
      simp only [d12228, d159804, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d12229 q = 1) (hb : d159762 q = 1) : d159805 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d12229, d159805, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12229, d159805, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d37 q = 1) (hb : d159762 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d37, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31401 q ha hb
    | true =>
      simp only [d37, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d38 q = 1) (hb : d159762 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d38, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d38, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d12230 q = 1) (hb : d159762 q = 1) : d159806 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d12230, d159806, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d12230, d159806, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d12231 q = 1) (hb : d159762 q = 1) : d159807 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d12231, d159807, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d12231, d159807, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d12232 q = 1) (hb : d159762 q = 1) : d159808 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d12232, d159808, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d12232, d159808, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d12240 q = 1) (hb : d159762 q = 1) : d159816 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d12240, d159816, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d12240, d159816, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro31424 (p : Pattern) (ha : d115247 p = 1) (hb : d159762 p = 1) : d159822 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d159762 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d117 q = 1) (hb : d159762 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d117, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31415 q ha hb
    | true =>
      simp only [d117, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d118 q = 1) (hb : d159762 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d119 q = 1) (hb : d159762 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d120 q = 1) (hb : d159762 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d124 q = 1) (hb : d159762 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31416 q ha hb
    | true =>
      simp only [d124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d125 q = 1) (hb : d159762 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d126 q = 1) (hb : d159762 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d12234 q = 1) (hb : d159762 q = 1) : d159810 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d12234, d159810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31419 q ha hb
    | true =>
      simp only [d12234, d159810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31402 q ha hb
  have h9 (q : Pattern) (ha : d115238 q = 1) (hb : d159762 q = 1) : d159811 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d115238, d159811, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d115238, d159811, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d43 q = 1) (hb : d159762 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d43, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31402 q ha hb
    | true =>
      simp only [d43, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d44 q = 1) (hb : d159762 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d44, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d44, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d115239 q = 1) (hb : d159762 q = 1) : d159812 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d115239, d159812, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d115239, d159812, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d115240 q = 1) (hb : d159762 q = 1) : d159813 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d115240, d159813, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d115240, d159813, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d115241 q = 1) (hb : d159762 q = 1) : d159814 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d115241, d159814, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d115241, d159814, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d195 q = 1) (hb : d159762 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d195, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31421 q ha hb
    | true =>
      simp only [d195, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h16 (q : Pattern) (ha : d196 q = 1) (hb : d159762 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d196, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d196, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d197 q = 1) (hb : d159762 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d197, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d197, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h18 (q : Pattern) (ha : d198 q = 1) (hb : d159762 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d198, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d198, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d200 q = 1) (hb : d159762 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d200, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31422 q ha hb
    | true =>
      simp only [d200, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h20 (q : Pattern) (ha : d201 q = 1) (hb : d159762 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d201, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d201, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
  have h21 (q : Pattern) (ha : d202 q = 1) (hb : d159762 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d202, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d202, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h22 (q : Pattern) (ha : d12241 q = 1) (hb : d159762 q = 1) : d159817 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d12241, d159817, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31423 q ha hb
    | true =>
      simp only [d12241, d159817, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31404 q ha hb
  have h23 (q : Pattern) (ha : d115243 q = 1) (hb : d159762 q = 1) : d159818 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d115243, d159818, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
    | true =>
      simp only [d115243, d159818, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h24 (q : Pattern) (ha : d50 q = 1) (hb : d159762 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d50, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31404 q ha hb
    | true =>
      simp only [d50, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h25 (q : Pattern) (ha : d51 q = 1) (hb : d159762 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d51, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q ha hb
    | true =>
      simp only [d51, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h26 (q : Pattern) (ha : d115244 q = 1) (hb : d159762 q = 1) : d159819 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d115244, d159819, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
    | true =>
      simp only [d115244, d159819, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q ha hb
  have h27 (q : Pattern) (ha : d115245 q = 1) (hb : d159762 q = 1) : d159820 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d115245, d159820, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d115245, d159820, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h26 q ha hb
  have h28 (q : Pattern) (ha : d115246 q = 1) (hb : d159762 q = 1) : d159821 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d115246, d159821, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d115246, d159821, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h27 q ha hb
  have h29 (q : Pattern) (ha : d115247 q = 1) (hb : d159762 q = 1) : d159822 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d115247, d159822, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d115247, d159822, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h28 q ha hb
  exact h29 p ha hb
theorem andIntro31425 (p : Pattern) (ha : d115254 p = 1) (hb : d159762 p = 1) : d159827 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d159762 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12241 q = 1) (hb : d159762 q = 1) : d159817 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d12241, d159817, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31423 q ha hb
    | true =>
      simp only [d12241, d159817, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31404 q ha hb
  have h2 (q : Pattern) (ha : d115243 q = 1) (hb : d159762 q = 1) : d159818 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d115243, d159818, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d115243, d159818, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d50 q = 1) (hb : d159762 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d50, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31404 q ha hb
    | true =>
      simp only [d50, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d51 q = 1) (hb : d159762 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d51, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d51, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d115244 q = 1) (hb : d159762 q = 1) : d159819 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d115244, d159819, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d115244, d159819, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d115252 q = 1) (hb : d159762 q = 1) : d159820 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d115252, d159820, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d115252, d159820, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d115253 q = 1) (hb : d159762 q = 1) : d159821 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d115253, d159821, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d115253, d159821, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d115254 q = 1) (hb : d159762 q = 1) : d159827 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d115254, d159827, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d115254, d159827, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro31426 (p : Pattern) (ha : d6078 p = 1) (hb : d159762 p = 1) : d159834 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d229 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d69 q = 1) (hb : d100904 q = 1) : d69 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d230 q = 1) (hb : d159761 q = 1) : d159833 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d230, d159761, d159833, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d230, d159761, d159833, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d6078 q = 1) (hb : d159762 q = 1) : d159834 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d6078, d159762, d159834, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d6078, d159762, d159834, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  exact h4 p ha hb
theorem andIntro31427 (p : Pattern) (ha : d12261 p = 1) (hb : d159762 p = 1) : d159840 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d159762 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d6079 q = 1) (hb : d159762 q = 1) : d159835 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d6079, d159835, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31426 q ha hb
    | true =>
      simp only [d6079, d159835, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31407 q ha hb
  have h2 (q : Pattern) (ha : d6080 q = 1) (hb : d159762 q = 1) : d159836 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d6080, d159836, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6080, d159836, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d6081 q = 1) (hb : d159762 q = 1) : d159837 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d6081, d159837, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6081, d159837, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d72 q = 1) (hb : d159762 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d72, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31407 q ha hb
    | true =>
      simp only [d72, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d73 q = 1) (hb : d159762 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d73, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d73, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d74 q = 1) (hb : d159762 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d74, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d74, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d12259 q = 1) (hb : d159762 q = 1) : d159838 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d12259, d159838, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d12259, d159838, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d75 q = 1) (hb : d159762 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d75, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d75, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d12260 q = 1) (hb : d159762 q = 1) : d159839 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d12260, d159839, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d12260, d159839, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d12261 q = 1) (hb : d159762 q = 1) : d159840 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d12261, d159840, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d12261, d159840, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h10 p ha hb
theorem andIntro31428 (p : Pattern) (ha : d12267 p = 1) (hb : d159762 p = 1) : d159846 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d159762 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12262 q = 1) (hb : d159762 q = 1) : d159841 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d12262, d159841, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31427 q ha hb
    | true =>
      simp only [d12262, d159841, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d12263 q = 1) (hb : d159762 q = 1) : d159842 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d12263, d159842, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12263, d159842, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d78 q = 1) (hb : d159762 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d78, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31408 q ha hb
    | true =>
      simp only [d78, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d79 q = 1) (hb : d159762 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d79, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d79, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d12264 q = 1) (hb : d159762 q = 1) : d159843 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d12264, d159843, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d12264, d159843, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d12265 q = 1) (hb : d159762 q = 1) : d159844 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d12265, d159844, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d12265, d159844, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d12266 q = 1) (hb : d159762 q = 1) : d159845 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d12266, d159845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d12266, d159845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d12267 q = 1) (hb : d159762 q = 1) : d159846 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d12267, d159846, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d12267, d159846, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro31429 (p : Pattern) (ha : d115264 p = 1) (hb : d159762 p = 1) : d159852 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d159762 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12268 q = 1) (hb : d159762 q = 1) : d159847 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d12268, d159847, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31428 q ha hb
    | true =>
      simp only [d12268, d159847, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31409 q ha hb
  have h2 (q : Pattern) (ha : d115260 q = 1) (hb : d159762 q = 1) : d159848 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d115260, d159848, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d115260, d159848, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d84 q = 1) (hb : d159762 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d84, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31409 q ha hb
    | true =>
      simp only [d84, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d85 q = 1) (hb : d159762 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d85, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d85, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d115261 q = 1) (hb : d159762 q = 1) : d159849 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d115261, d159849, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d115261, d159849, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d115262 q = 1) (hb : d159762 q = 1) : d159850 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d115262, d159850, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d115262, d159850, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d115263 q = 1) (hb : d159762 q = 1) : d159851 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d115263, d159851, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d115263, d159851, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d115264 q = 1) (hb : d159762 q = 1) : d159852 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d115264, d159852, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d115264, d159852, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro31430 (p : Pattern) (ha : d115270 p = 1) (hb : d159762 p = 1) : d159858 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d159762 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d105 q = 1) (hb : d159762 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d105, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d105, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31412 q ha hb
  have h2 (q : Pattern) (ha : d106 q = 1) (hb : d159762 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d106, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d106, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d112 q = 1) (hb : d159762 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31412 q ha hb
    | true =>
      simp only [d112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31413 q ha hb
  have h4 (q : Pattern) (ha : d113 q = 1) (hb : d159762 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d114 q = 1) (hb : d159762 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d114, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d114, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d115248 q = 1) (hb : d159762 q = 1) : d159823 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d115248, d159823, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31420 q ha hb
    | true =>
      simp only [d115248, d159823, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31424 q ha hb
  have h7 (q : Pattern) (ha : d214 q = 1) (hb : d159762 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d214, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31414 q ha hb
    | true =>
      simp only [d214, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d115249 q = 1) (hb : d159762 q = 1) : d159824 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d115249, d159824, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d115249, d159824, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d115250 q = 1) (hb : d159762 q = 1) : d159825 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d115250, d159825, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d115250, d159825, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d115251 q = 1) (hb : d159762 q = 1) : d159826 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d115251, d159826, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d115251, d159826, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d115255 q = 1) (hb : d159762 q = 1) : d159828 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d115255, d159828, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d115255, d159828, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31425 q ha hb
  have h12 (q : Pattern) (ha : d115256 q = 1) (hb : d159762 q = 1) : d159829 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d115256, d159829, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d115256, d159829, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d115257 q = 1) (hb : d159762 q = 1) : d159830 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d115257, d159830, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d115257, d159830, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d115258 q = 1) (hb : d159762 q = 1) : d159831 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d115258, d159831, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d115258, d159831, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d115259 q = 1) (hb : d159762 q = 1) : d159832 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d115259, d159832, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d115259, d159832, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d115265 q = 1) (hb : d159762 q = 1) : d159853 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d115265, d159853, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d115265, d159853, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31429 q ha hb
  have h17 (q : Pattern) (ha : d115266 q = 1) (hb : d159762 q = 1) : d159854 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d115266, d159854, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d115266, d159854, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h18 (q : Pattern) (ha : d115267 q = 1) (hb : d159762 q = 1) : d159855 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d115267, d159855, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d115267, d159855, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h19 (q : Pattern) (ha : d115268 q = 1) (hb : d159762 q = 1) : d159856 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d115268, d159856, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d115268, d159856, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h20 (q : Pattern) (ha : d115269 q = 1) (hb : d159762 q = 1) : d159857 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d115269, d159857, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d115269, d159857, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h21 (q : Pattern) (ha : d115270 q = 1) (hb : d159762 q = 1) : d159858 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d115270, d159858, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d115270, d159858, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
  exact h21 p ha hb
theorem andIntro31431 (p : Pattern) (ha : d406 p = 1) (hb : d159762 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d159762 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d50 q = 1) (hb : d159762 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d50, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31404 q ha hb
    | true =>
      simp only [d50, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d107 q = 1) (hb : d159762 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d107, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d107, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d108 q = 1) (hb : d159762 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d108, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d108, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d109 q = 1) (hb : d159762 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d109, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d109, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d110 q = 1) (hb : d159762 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d110, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d110, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d406 q = 1) (hb : d159762 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d406, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d406, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro31432 (p : Pattern) (ha : d462 p = 1) (hb : d159762 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d159762 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d84 q = 1) (hb : d159762 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d84, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31409 q ha hb
    | true =>
      simp only [d84, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d458 q = 1) (hb : d159762 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d458, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d458, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d459 q = 1) (hb : d159762 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d459, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d459, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d460 q = 1) (hb : d159762 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d460, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d460, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d461 q = 1) (hb : d159762 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d461, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d461, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d462 q = 1) (hb : d159762 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d462, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d462, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro31433 (p : Pattern) (ha : d12289 p = 1) (hb : d159762 p = 1) : d159868 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d159762 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12234 q = 1) (hb : d159762 q = 1) : d159810 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d12234, d159810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31419 q ha hb
    | true =>
      simp only [d12234, d159810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31402 q ha hb
  have h2 (q : Pattern) (ha : d12285 q = 1) (hb : d159762 q = 1) : d159864 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d12285, d159864, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12285, d159864, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d12286 q = 1) (hb : d159762 q = 1) : d159865 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d12286, d159865, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d12286, d159865, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d12287 q = 1) (hb : d159762 q = 1) : d159866 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d12287, d159866, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12287, d159866, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d12288 q = 1) (hb : d159762 q = 1) : d159867 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d12288, d159867, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12288, d159867, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d12289 q = 1) (hb : d159762 q = 1) : d159868 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d12289, d159868, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12289, d159868, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro31434 (p : Pattern) (ha : d12296 p = 1) (hb : d159762 p = 1) : d159875 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d159762 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12234 q = 1) (hb : d159762 q = 1) : d159810 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d12234, d159810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31419 q ha hb
    | true =>
      simp only [d12234, d159810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31402 q ha hb
  have h2 (q : Pattern) (ha : d12285 q = 1) (hb : d159762 q = 1) : d159864 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d12285, d159864, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12285, d159864, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d12286 q = 1) (hb : d159762 q = 1) : d159865 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d12286, d159865, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d12286, d159865, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d12287 q = 1) (hb : d159762 q = 1) : d159866 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d12287, d159866, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12287, d159866, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d12288 q = 1) (hb : d159762 q = 1) : d159867 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d12288, d159867, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12288, d159867, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d12241 q = 1) (hb : d159762 q = 1) : d159817 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d12241, d159817, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31423 q ha hb
    | true =>
      simp only [d12241, d159817, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31404 q ha hb
  have h7 (q : Pattern) (ha : d12292 q = 1) (hb : d159762 q = 1) : d159871 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d12292, d159871, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12292, d159871, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d12293 q = 1) (hb : d159762 q = 1) : d159872 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d12293, d159872, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d12293, d159872, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d12294 q = 1) (hb : d159762 q = 1) : d159873 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d12294, d159873, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12294, d159873, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d12295 q = 1) (hb : d159762 q = 1) : d159874 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d12295, d159874, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12295, d159874, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d12296 q = 1) (hb : d159762 q = 1) : d159875 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d12296, d159875, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d12296, d159875, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro31435 (p : Pattern) (ha : d12373 p = 1) (hb : d159762 p = 1) : d159928 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d159762 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12234 q = 1) (hb : d159762 q = 1) : d159810 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d12234, d159810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31419 q ha hb
    | true =>
      simp only [d12234, d159810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31402 q ha hb
  have h2 (q : Pattern) (ha : d12285 q = 1) (hb : d159762 q = 1) : d159864 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d12285, d159864, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12285, d159864, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d12286 q = 1) (hb : d159762 q = 1) : d159865 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d12286, d159865, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d12286, d159865, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d12287 q = 1) (hb : d159762 q = 1) : d159866 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d12287, d159866, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12287, d159866, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d12288 q = 1) (hb : d159762 q = 1) : d159867 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d12288, d159867, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12288, d159867, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d43 q = 1) (hb : d159762 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d43, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31402 q ha hb
    | true =>
      simp only [d43, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d100 q = 1) (hb : d159762 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d100, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d100, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d101 q = 1) (hb : d159762 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d101, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d101, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d102 q = 1) (hb : d159762 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d103 q = 1) (hb : d159762 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d12373 q = 1) (hb : d159762 q = 1) : d159928 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d12373, d159928, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d12373, d159928, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro31436 (p : Pattern) (ha : d12301 p = 1) (hb : d159762 p = 1) : d159880 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d159762 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12228 q = 1) (hb : d159762 q = 1) : d159804 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d12228, d159804, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31418 q ha hb
    | true =>
      simp only [d12228, d159804, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d12229 q = 1) (hb : d159762 q = 1) : d159805 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d12229, d159805, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12229, d159805, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d37 q = 1) (hb : d159762 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d37, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31401 q ha hb
    | true =>
      simp only [d37, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d38 q = 1) (hb : d159762 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d38, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d38, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d12230 q = 1) (hb : d159762 q = 1) : d159806 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d12230, d159806, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d12230, d159806, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d12231 q = 1) (hb : d159762 q = 1) : d159807 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d12231, d159807, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d12231, d159807, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d12300 q = 1) (hb : d159762 q = 1) : d159879 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d12300, d159879, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12300, d159879, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d12301 q = 1) (hb : d159762 q = 1) : d159880 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d12301, d159880, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12301, d159880, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro31437 (p : Pattern) (ha : d12308 p = 1) (hb : d159762 p = 1) : d159887 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d159762 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12228 q = 1) (hb : d159762 q = 1) : d159804 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d12228, d159804, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31418 q ha hb
    | true =>
      simp only [d12228, d159804, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d12229 q = 1) (hb : d159762 q = 1) : d159805 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d12229, d159805, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12229, d159805, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d37 q = 1) (hb : d159762 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d37, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31401 q ha hb
    | true =>
      simp only [d37, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d38 q = 1) (hb : d159762 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d38, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d38, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d12230 q = 1) (hb : d159762 q = 1) : d159806 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d12230, d159806, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d12230, d159806, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d12306 q = 1) (hb : d159762 q = 1) : d159885 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d12306, d159885, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12306, d159885, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d12307 q = 1) (hb : d159762 q = 1) : d159886 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d12307, d159886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d12307, d159886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d12308 q = 1) (hb : d159762 q = 1) : d159887 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d12308, d159887, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12308, d159887, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro31438 (p : Pattern) (ha : d12312 p = 1) (hb : d159762 p = 1) : d159892 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d322 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d142 q = 1) (hb : d100904 q = 1) : d142 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d323 q = 1) (hb : d159761 q = 1) : d159891 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d323, d159761, d159891, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d323, d159761, d159891, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d12312 q = 1) (hb : d159762 q = 1) : d159892 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d12312, d159762, d159892, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d12312, d159762, d159892, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  exact h4 p ha hb
theorem andIntro31439 (p : Pattern) (ha : d12318 p = 1) (hb : d159762 p = 1) : d159898 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d159762 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12313 q = 1) (hb : d159762 q = 1) : d159893 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d12313, d159893, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31438 q ha hb
    | true =>
      simp only [d12313, d159893, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31417 q ha hb
  have h2 (q : Pattern) (ha : d12314 q = 1) (hb : d159762 q = 1) : d159894 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d12314, d159894, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12314, d159894, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d12315 q = 1) (hb : d159762 q = 1) : d159895 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d12315, d159895, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12315, d159895, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d4819 q = 1) (hb : d159762 q = 1) : d159798 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d4819, d159798, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31417 q ha hb
    | true =>
      simp only [d4819, d159798, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31400 q ha hb
  have h5 (q : Pattern) (ha : d4820 q = 1) (hb : d159762 q = 1) : d159799 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d4820, d159799, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4820, d159799, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d4821 q = 1) (hb : d159762 q = 1) : d159800 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d4821, d159800, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4821, d159800, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d12316 q = 1) (hb : d159762 q = 1) : d159896 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d12316, d159896, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d12316, d159896, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d31 q = 1) (hb : d159762 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d31, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31400 q ha hb
    | true =>
      simp only [d31, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d32 q = 1) (hb : d159762 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d32, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d32, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d33 q = 1) (hb : d159762 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d33, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d33, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d12225 q = 1) (hb : d159762 q = 1) : d159801 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d12225, d159801, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d12225, d159801, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d12317 q = 1) (hb : d159762 q = 1) : d159897 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d12317, d159897, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d12317, d159897, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d12318 q = 1) (hb : d159762 q = 1) : d159898 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d12318, d159898, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d12318, d159898, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h13 p ha hb
theorem andIntro31440 (p : Pattern) (ha : d12324 p = 1) (hb : d159762 p = 1) : d159904 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d159762 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12319 q = 1) (hb : d159762 q = 1) : d159899 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d12319, d159899, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31439 q ha hb
    | true =>
      simp only [d12319, d159899, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d12320 q = 1) (hb : d159762 q = 1) : d159900 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d12320, d159900, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12320, d159900, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d12228 q = 1) (hb : d159762 q = 1) : d159804 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d12228, d159804, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31418 q ha hb
    | true =>
      simp only [d12228, d159804, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d12229 q = 1) (hb : d159762 q = 1) : d159805 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d12229, d159805, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12229, d159805, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d12321 q = 1) (hb : d159762 q = 1) : d159901 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d12321, d159901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d12321, d159901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d12322 q = 1) (hb : d159762 q = 1) : d159902 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d12322, d159902, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d12322, d159902, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d12323 q = 1) (hb : d159762 q = 1) : d159903 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d12323, d159903, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d12323, d159903, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d12324 q = 1) (hb : d159762 q = 1) : d159904 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d12324, d159904, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12324, d159904, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro31441 (p : Pattern) (ha : d12344 p = 1) (hb : d159762 p = 1) : d159809 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d159762 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12228 q = 1) (hb : d159762 q = 1) : d159804 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d12228, d159804, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31418 q ha hb
    | true =>
      simp only [d12228, d159804, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d12229 q = 1) (hb : d159762 q = 1) : d159805 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d12229, d159805, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12229, d159805, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d12341 q = 1) (hb : d159762 q = 1) : d159806 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d12341, d159806, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d12341, d159806, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d12342 q = 1) (hb : d159762 q = 1) : d159807 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d12342, d159807, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d12342, d159807, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d12343 q = 1) (hb : d159762 q = 1) : d159808 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d12343, d159808, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d12343, d159808, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d12344 q = 1) (hb : d159762 q = 1) : d159809 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d12344, d159809, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12344, d159809, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro31442 (p : Pattern) (ha : d115280 p = 1) (hb : d159762 p = 1) : d159910 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d159762 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12302 q = 1) (hb : d159762 q = 1) : d159881 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d12302, d159881, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31436 q ha hb
    | true =>
      simp only [d12302, d159881, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31415 q ha hb
  have h2 (q : Pattern) (ha : d12303 q = 1) (hb : d159762 q = 1) : d159882 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d12303, d159882, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12303, d159882, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d12304 q = 1) (hb : d159762 q = 1) : d159883 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d12304, d159883, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d12304, d159883, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d12305 q = 1) (hb : d159762 q = 1) : d159884 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d12305, d159884, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12305, d159884, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d12309 q = 1) (hb : d159762 q = 1) : d159888 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d12309, d159888, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31437 q ha hb
    | true =>
      simp only [d12309, d159888, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31416 q ha hb
  have h6 (q : Pattern) (ha : d12310 q = 1) (hb : d159762 q = 1) : d159889 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d12310, d159889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12310, d159889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d12311 q = 1) (hb : d159762 q = 1) : d159890 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d12311, d159890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d12311, d159890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d12325 q = 1) (hb : d159762 q = 1) : d159905 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d12325, d159905, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31440 q ha hb
    | true =>
      simp only [d12325, d159905, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31419 q ha hb
  have h9 (q : Pattern) (ha : d115276 q = 1) (hb : d159762 q = 1) : d159906 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d115276, d159906, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d115276, d159906, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d12345 q = 1) (hb : d159762 q = 1) : d159810 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d12345, d159810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31441 q ha hb
    | true =>
      simp only [d12345, d159810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d12346 q = 1) (hb : d159762 q = 1) : d159811 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d12346, d159811, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d12346, d159811, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d115277 q = 1) (hb : d159762 q = 1) : d159907 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d115277, d159907, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d115277, d159907, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d115278 q = 1) (hb : d159762 q = 1) : d159908 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d115278, d159908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d115278, d159908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d115279 q = 1) (hb : d159762 q = 1) : d159909 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d115279, d159909, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d115279, d159909, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d115280 q = 1) (hb : d159762 q = 1) : d159910 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d115280, d159910, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d115280, d159910, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro31443 (p : Pattern) (ha : d12351 p = 1) (hb : d159762 p = 1) : d159911 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d159762 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12228 q = 1) (hb : d159762 q = 1) : d159804 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d12228, d159804, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31418 q ha hb
    | true =>
      simp only [d12228, d159804, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d12229 q = 1) (hb : d159762 q = 1) : d159805 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d12229, d159805, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12229, d159805, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d37 q = 1) (hb : d159762 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d37, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31401 q ha hb
    | true =>
      simp only [d37, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d38 q = 1) (hb : d159762 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d38, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d38, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d12230 q = 1) (hb : d159762 q = 1) : d159806 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d12230, d159806, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d12230, d159806, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d12231 q = 1) (hb : d159762 q = 1) : d159807 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d12231, d159807, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d12231, d159807, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d12300 q = 1) (hb : d159762 q = 1) : d159879 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d12300, d159879, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12300, d159879, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d12351 q = 1) (hb : d159762 q = 1) : d159911 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d12351, d159911, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d12351, d159911, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro31444 (p : Pattern) (ha : d12356 p = 1) (hb : d159762 p = 1) : d159916 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d159762 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12228 q = 1) (hb : d159762 q = 1) : d159804 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d12228, d159804, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31418 q ha hb
    | true =>
      simp only [d12228, d159804, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d12229 q = 1) (hb : d159762 q = 1) : d159805 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d12229, d159805, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12229, d159805, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d37 q = 1) (hb : d159762 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d37, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31401 q ha hb
    | true =>
      simp only [d37, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d38 q = 1) (hb : d159762 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d38, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d38, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d12230 q = 1) (hb : d159762 q = 1) : d159806 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d12230, d159806, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d12230, d159806, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d12306 q = 1) (hb : d159762 q = 1) : d159885 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d12306, d159885, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12306, d159885, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d12307 q = 1) (hb : d159762 q = 1) : d159886 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d12307, d159886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d12307, d159886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d12356 q = 1) (hb : d159762 q = 1) : d159916 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d12356, d159916, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d12356, d159916, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro31445 (p : Pattern) (ha : d12360 p = 1) (hb : d159762 p = 1) : d159920 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d159762 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12319 q = 1) (hb : d159762 q = 1) : d159899 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d12319, d159899, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31439 q ha hb
    | true =>
      simp only [d12319, d159899, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d12320 q = 1) (hb : d159762 q = 1) : d159900 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d12320, d159900, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12320, d159900, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d12228 q = 1) (hb : d159762 q = 1) : d159804 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d12228, d159804, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31418 q ha hb
    | true =>
      simp only [d12228, d159804, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d12229 q = 1) (hb : d159762 q = 1) : d159805 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d12229, d159805, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12229, d159805, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d12321 q = 1) (hb : d159762 q = 1) : d159901 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d12321, d159901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d12321, d159901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d12322 q = 1) (hb : d159762 q = 1) : d159902 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d12322, d159902, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d12322, d159902, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d12323 q = 1) (hb : d159762 q = 1) : d159903 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d12323, d159903, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d12323, d159903, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d12360 q = 1) (hb : d159762 q = 1) : d159920 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d12360, d159920, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d12360, d159920, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro31446 (p : Pattern) (ha : d12365 p = 1) (hb : d159762 p = 1) : d159816 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d159762 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12228 q = 1) (hb : d159762 q = 1) : d159804 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d12228, d159804, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31418 q ha hb
    | true =>
      simp only [d12228, d159804, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d12229 q = 1) (hb : d159762 q = 1) : d159805 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d12229, d159805, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12229, d159805, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d12341 q = 1) (hb : d159762 q = 1) : d159806 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d12341, d159806, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d12341, d159806, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d12342 q = 1) (hb : d159762 q = 1) : d159807 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d12342, d159807, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d12342, d159807, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d12343 q = 1) (hb : d159762 q = 1) : d159808 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d12343, d159808, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d12343, d159808, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d12365 q = 1) (hb : d159762 q = 1) : d159816 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d12365, d159816, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d12365, d159816, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro31447 (p : Pattern) (ha : d115285 p = 1) (hb : d159762 p = 1) : d159926 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d159762 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12302 q = 1) (hb : d159762 q = 1) : d159881 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d12302, d159881, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31436 q ha hb
    | true =>
      simp only [d12302, d159881, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31415 q ha hb
  have h2 (q : Pattern) (ha : d12303 q = 1) (hb : d159762 q = 1) : d159882 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d12303, d159882, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12303, d159882, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d12304 q = 1) (hb : d159762 q = 1) : d159883 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d12304, d159883, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d12304, d159883, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d12305 q = 1) (hb : d159762 q = 1) : d159884 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d12305, d159884, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12305, d159884, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d12309 q = 1) (hb : d159762 q = 1) : d159888 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d12309, d159888, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31437 q ha hb
    | true =>
      simp only [d12309, d159888, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31416 q ha hb
  have h6 (q : Pattern) (ha : d12310 q = 1) (hb : d159762 q = 1) : d159889 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d12310, d159889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12310, d159889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d12311 q = 1) (hb : d159762 q = 1) : d159890 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d12311, d159890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d12311, d159890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d12325 q = 1) (hb : d159762 q = 1) : d159905 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d12325, d159905, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31440 q ha hb
    | true =>
      simp only [d12325, d159905, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31419 q ha hb
  have h9 (q : Pattern) (ha : d115276 q = 1) (hb : d159762 q = 1) : d159906 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d115276, d159906, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d115276, d159906, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d12345 q = 1) (hb : d159762 q = 1) : d159810 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d12345, d159810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31441 q ha hb
    | true =>
      simp only [d12345, d159810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d12346 q = 1) (hb : d159762 q = 1) : d159811 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d12346, d159811, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d12346, d159811, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d115277 q = 1) (hb : d159762 q = 1) : d159907 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d115277, d159907, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d115277, d159907, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d115278 q = 1) (hb : d159762 q = 1) : d159908 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d115278, d159908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d115278, d159908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d115279 q = 1) (hb : d159762 q = 1) : d159909 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d115279, d159909, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d115279, d159909, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d12352 q = 1) (hb : d159762 q = 1) : d159912 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d12352, d159912, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31443 q ha hb
    | true =>
      simp only [d12352, d159912, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31421 q ha hb
  have h16 (q : Pattern) (ha : d12353 q = 1) (hb : d159762 q = 1) : d159913 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d12353, d159913, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12353, d159913, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d12354 q = 1) (hb : d159762 q = 1) : d159914 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d12354, d159914, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d12354, d159914, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h18 (q : Pattern) (ha : d12355 q = 1) (hb : d159762 q = 1) : d159915 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d12355, d159915, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12355, d159915, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d12357 q = 1) (hb : d159762 q = 1) : d159917 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d12357, d159917, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31444 q ha hb
    | true =>
      simp only [d12357, d159917, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31422 q ha hb
  have h20 (q : Pattern) (ha : d12358 q = 1) (hb : d159762 q = 1) : d159918 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d12358, d159918, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12358, d159918, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
  have h21 (q : Pattern) (ha : d12359 q = 1) (hb : d159762 q = 1) : d159919 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d12359, d159919, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d12359, d159919, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h22 (q : Pattern) (ha : d12361 q = 1) (hb : d159762 q = 1) : d159921 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d12361, d159921, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31445 q ha hb
    | true =>
      simp only [d12361, d159921, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31423 q ha hb
  have h23 (q : Pattern) (ha : d115281 q = 1) (hb : d159762 q = 1) : d159922 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d115281, d159922, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
    | true =>
      simp only [d115281, d159922, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h24 (q : Pattern) (ha : d12366 q = 1) (hb : d159762 q = 1) : d159817 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d12366, d159817, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31446 q ha hb
    | true =>
      simp only [d12366, d159817, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h25 (q : Pattern) (ha : d12367 q = 1) (hb : d159762 q = 1) : d159818 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d12367, d159818, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q ha hb
    | true =>
      simp only [d12367, d159818, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h26 (q : Pattern) (ha : d115282 q = 1) (hb : d159762 q = 1) : d159923 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d115282, d159923, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
    | true =>
      simp only [d115282, d159923, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q ha hb
  have h27 (q : Pattern) (ha : d115283 q = 1) (hb : d159762 q = 1) : d159924 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d115283, d159924, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d115283, d159924, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h26 q ha hb
  have h28 (q : Pattern) (ha : d115284 q = 1) (hb : d159762 q = 1) : d159925 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d115284, d159925, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d115284, d159925, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h27 q ha hb
  have h29 (q : Pattern) (ha : d115285 q = 1) (hb : d159762 q = 1) : d159926 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d115285, d159926, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d115285, d159926, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h28 q ha hb
  exact h29 p ha hb
theorem andIntro31448 (p : Pattern) (ha : d115292 p = 1) (hb : d159762 p = 1) : d159935 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d159762 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12361 q = 1) (hb : d159762 q = 1) : d159921 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d12361, d159921, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31445 q ha hb
    | true =>
      simp only [d12361, d159921, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31423 q ha hb
  have h2 (q : Pattern) (ha : d115281 q = 1) (hb : d159762 q = 1) : d159922 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d115281, d159922, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d115281, d159922, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d12366 q = 1) (hb : d159762 q = 1) : d159817 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d12366, d159817, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31446 q ha hb
    | true =>
      simp only [d12366, d159817, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d12367 q = 1) (hb : d159762 q = 1) : d159818 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d12367, d159818, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d12367, d159818, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d115282 q = 1) (hb : d159762 q = 1) : d159923 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d115282, d159923, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d115282, d159923, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d115290 q = 1) (hb : d159762 q = 1) : d159933 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d115290, d159933, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d115290, d159933, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d115291 q = 1) (hb : d159762 q = 1) : d159934 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d115291, d159934, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d115291, d159934, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d115292 q = 1) (hb : d159762 q = 1) : d159935 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d115292, d159935, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d115292, d159935, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro31449 (p : Pattern) (ha : d12386 p = 1) (hb : d159762 p = 1) : d159942 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d415 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d229 q = 1) (hb : d100904 q = 1) : d229 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d416 q = 1) (hb : d159761 q = 1) : d159941 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d416, d159761, d159941, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d416, d159761, d159941, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d12386 q = 1) (hb : d159762 q = 1) : d159942 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d12386, d159762, d159942, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d12386, d159762, d159942, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  exact h4 p ha hb
theorem andIntro31450 (p : Pattern) (ha : d12392 p = 1) (hb : d159762 p = 1) : d159948 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d159762 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12387 q = 1) (hb : d159762 q = 1) : d159943 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d12387, d159943, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31449 q ha hb
    | true =>
      simp only [d12387, d159943, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31426 q ha hb
  have h2 (q : Pattern) (ha : d12388 q = 1) (hb : d159762 q = 1) : d159944 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d12388, d159944, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12388, d159944, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d12389 q = 1) (hb : d159762 q = 1) : d159945 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d12389, d159945, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12389, d159945, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d6079 q = 1) (hb : d159762 q = 1) : d159835 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d6079, d159835, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31426 q ha hb
    | true =>
      simp only [d6079, d159835, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31407 q ha hb
  have h5 (q : Pattern) (ha : d6080 q = 1) (hb : d159762 q = 1) : d159836 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d6080, d159836, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6080, d159836, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d6081 q = 1) (hb : d159762 q = 1) : d159837 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d6081, d159837, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6081, d159837, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d12390 q = 1) (hb : d159762 q = 1) : d159946 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d12390, d159946, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d12390, d159946, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d72 q = 1) (hb : d159762 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d72, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31407 q ha hb
    | true =>
      simp only [d72, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d73 q = 1) (hb : d159762 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d73, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d73, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d74 q = 1) (hb : d159762 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d74, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d74, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d12259 q = 1) (hb : d159762 q = 1) : d159838 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d12259, d159838, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d12259, d159838, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d12391 q = 1) (hb : d159762 q = 1) : d159947 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d12391, d159947, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d12391, d159947, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d12392 q = 1) (hb : d159762 q = 1) : d159948 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d12392, d159948, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d12392, d159948, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h13 p ha hb
theorem andIntro31451 (p : Pattern) (ha : d12398 p = 1) (hb : d159762 p = 1) : d159954 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d159762 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12393 q = 1) (hb : d159762 q = 1) : d159949 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d12393, d159949, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31450 q ha hb
    | true =>
      simp only [d12393, d159949, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d12394 q = 1) (hb : d159762 q = 1) : d159950 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d12394, d159950, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12394, d159950, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d12262 q = 1) (hb : d159762 q = 1) : d159841 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d12262, d159841, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31427 q ha hb
    | true =>
      simp only [d12262, d159841, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d12263 q = 1) (hb : d159762 q = 1) : d159842 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d12263, d159842, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12263, d159842, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d12395 q = 1) (hb : d159762 q = 1) : d159951 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d12395, d159951, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d12395, d159951, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d12396 q = 1) (hb : d159762 q = 1) : d159952 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d12396, d159952, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d12396, d159952, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d12397 q = 1) (hb : d159762 q = 1) : d159953 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d12397, d159953, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d12397, d159953, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d12398 q = 1) (hb : d159762 q = 1) : d159954 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d12398, d159954, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d12398, d159954, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro31452 (p : Pattern) (ha : d12418 p = 1) (hb : d159762 p = 1) : d159846 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d159762 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12262 q = 1) (hb : d159762 q = 1) : d159841 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d12262, d159841, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31427 q ha hb
    | true =>
      simp only [d12262, d159841, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d12263 q = 1) (hb : d159762 q = 1) : d159842 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d12263, d159842, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12263, d159842, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d12415 q = 1) (hb : d159762 q = 1) : d159843 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d12415, d159843, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d12415, d159843, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d12416 q = 1) (hb : d159762 q = 1) : d159844 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d12416, d159844, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d12416, d159844, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d12417 q = 1) (hb : d159762 q = 1) : d159845 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d12417, d159845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d12417, d159845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d12418 q = 1) (hb : d159762 q = 1) : d159846 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d12418, d159846, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d12418, d159846, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro31453 (p : Pattern) (ha : d115302 p = 1) (hb : d159762 p = 1) : d159960 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d159762 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12399 q = 1) (hb : d159762 q = 1) : d159955 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d12399, d159955, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31451 q ha hb
    | true =>
      simp only [d12399, d159955, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31428 q ha hb
  have h2 (q : Pattern) (ha : d115298 q = 1) (hb : d159762 q = 1) : d159956 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d115298, d159956, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d115298, d159956, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d12419 q = 1) (hb : d159762 q = 1) : d159847 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d12419, d159847, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31452 q ha hb
    | true =>
      simp only [d12419, d159847, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d12420 q = 1) (hb : d159762 q = 1) : d159848 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d12420, d159848, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d12420, d159848, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d115299 q = 1) (hb : d159762 q = 1) : d159957 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d115299, d159957, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d115299, d159957, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d115300 q = 1) (hb : d159762 q = 1) : d159958 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d115300, d159958, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d115300, d159958, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d115301 q = 1) (hb : d159762 q = 1) : d159959 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d115301, d159959, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d115301, d159959, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d115302 q = 1) (hb : d159762 q = 1) : d159960 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d115302, d159960, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d115302, d159960, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro31454 (p : Pattern) (ha : d115308 p = 1) (hb : d159762 p = 1) : d159966 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d159762 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12290 q = 1) (hb : d159762 q = 1) : d159869 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d12290, d159869, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12290, d159869, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31433 q ha hb
  have h2 (q : Pattern) (ha : d12291 q = 1) (hb : d159762 q = 1) : d159870 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d12291, d159870, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d12291, d159870, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d12297 q = 1) (hb : d159762 q = 1) : d159876 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d12297, d159876, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31433 q ha hb
    | true =>
      simp only [d12297, d159876, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31434 q ha hb
  have h4 (q : Pattern) (ha : d12298 q = 1) (hb : d159762 q = 1) : d159877 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d12298, d159877, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d12298, d159877, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d12299 q = 1) (hb : d159762 q = 1) : d159878 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d12299, d159878, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d12299, d159878, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d115286 q = 1) (hb : d159762 q = 1) : d159927 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d115286, d159927, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31442 q ha hb
    | true =>
      simp only [d115286, d159927, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31447 q ha hb
  have h7 (q : Pattern) (ha : d12374 q = 1) (hb : d159762 q = 1) : d159929 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d12374, d159929, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31435 q ha hb
    | true =>
      simp only [d12374, d159929, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31413 q ha hb
  have h8 (q : Pattern) (ha : d115287 q = 1) (hb : d159762 q = 1) : d159930 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d115287, d159930, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d115287, d159930, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d115288 q = 1) (hb : d159762 q = 1) : d159931 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d115288, d159931, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d115288, d159931, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d115289 q = 1) (hb : d159762 q = 1) : d159932 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d115289, d159932, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d115289, d159932, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d115293 q = 1) (hb : d159762 q = 1) : d159936 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d115293, d159936, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d115293, d159936, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31448 q ha hb
  have h12 (q : Pattern) (ha : d407 q = 1) (hb : d159762 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31431 q ha hb
  have h13 (q : Pattern) (ha : d115294 q = 1) (hb : d159762 q = 1) : d159937 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d115294, d159937, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d115294, d159937, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d115295 q = 1) (hb : d159762 q = 1) : d159938 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d115295, d159938, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d115295, d159938, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d115296 q = 1) (hb : d159762 q = 1) : d159939 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d115296, d159939, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d115296, d159939, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h16 (q : Pattern) (ha : d115297 q = 1) (hb : d159762 q = 1) : d159940 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d115297, d159940, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d115297, d159940, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d115303 q = 1) (hb : d159762 q = 1) : d159961 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d115303, d159961, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d115303, d159961, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31453 q ha hb
  have h18 (q : Pattern) (ha : d463 q = 1) (hb : d159762 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d463, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d463, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31432 q ha hb
  have h19 (q : Pattern) (ha : d115304 q = 1) (hb : d159762 q = 1) : d159962 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d115304, d159962, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d115304, d159962, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d115305 q = 1) (hb : d159762 q = 1) : d159963 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d115305, d159963, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d115305, d159963, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h21 (q : Pattern) (ha : d115306 q = 1) (hb : d159762 q = 1) : d159964 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d115306, d159964, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d115306, d159964, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h22 (q : Pattern) (ha : d115307 q = 1) (hb : d159762 q = 1) : d159965 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d115307, d159965, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d115307, d159965, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h23 (q : Pattern) (ha : d115308 q = 1) (hb : d159762 q = 1) : d159966 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d115308, d159966, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d115308, d159966, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
  exact h23 p ha hb
theorem andIntro31455 (p : Pattern) (ha : d115314 p = 1) (hb : d159762 p = 1) : d159972 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d159762 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d96 q = 1) (hb : d159762 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d96, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d96, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31411 q ha hb
  have h2 (q : Pattern) (ha : d97 q = 1) (hb : d159762 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d97, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d97, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d98 q = 1) (hb : d159762 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d98, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d98, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d99 q = 1) (hb : d159762 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d99, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d99, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d115271 q = 1) (hb : d159762 q = 1) : d159859 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d115271, d159859, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d115271, d159859, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31430 q ha hb
  have h6 (q : Pattern) (ha : d115272 q = 1) (hb : d159762 q = 1) : d159860 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d115272, d159860, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d115272, d159860, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d115273 q = 1) (hb : d159762 q = 1) : d159861 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d115273, d159861, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d115273, d159861, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d115274 q = 1) (hb : d159762 q = 1) : d159862 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d115274, d159862, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d115274, d159862, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d115275 q = 1) (hb : d159762 q = 1) : d159863 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d115275, d159863, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d115275, d159863, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d115309 q = 1) (hb : d159762 q = 1) : d159967 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d115309, d159967, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d115309, d159967, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31454 q ha hb
  have h11 (q : Pattern) (ha : d115310 q = 1) (hb : d159762 q = 1) : d159968 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d115310, d159968, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d115310, d159968, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d115311 q = 1) (hb : d159762 q = 1) : d159969 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d115311, d159969, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d115311, d159969, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d115312 q = 1) (hb : d159762 q = 1) : d159970 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d115312, d159970, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d115312, d159970, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d115313 q = 1) (hb : d159762 q = 1) : d159971 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d115313, d159971, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d115313, d159971, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d115314 q = 1) (hb : d159762 q = 1) : d159972 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d115314, d159972, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d115314, d159972, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro31456 (p : Pattern) (ha : d12438 p = 1) (hb : d159762 p = 1) : d159898 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d159762 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12313 q = 1) (hb : d159762 q = 1) : d159893 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d12313, d159893, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31438 q ha hb
    | true =>
      simp only [d12313, d159893, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31417 q ha hb
  have h2 (q : Pattern) (ha : d12314 q = 1) (hb : d159762 q = 1) : d159894 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d12314, d159894, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12314, d159894, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d12315 q = 1) (hb : d159762 q = 1) : d159895 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d12315, d159895, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12315, d159895, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d4819 q = 1) (hb : d159762 q = 1) : d159798 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d4819, d159798, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31417 q ha hb
    | true =>
      simp only [d4819, d159798, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31400 q ha hb
  have h5 (q : Pattern) (ha : d4820 q = 1) (hb : d159762 q = 1) : d159799 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d4820, d159799, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4820, d159799, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d4821 q = 1) (hb : d159762 q = 1) : d159800 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d4821, d159800, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4821, d159800, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d12316 q = 1) (hb : d159762 q = 1) : d159896 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d12316, d159896, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d12316, d159896, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d4822 q = 1) (hb : d159762 q = 1) : d159801 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d4822, d159801, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d4822, d159801, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d12437 q = 1) (hb : d159762 q = 1) : d159897 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d12437, d159897, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d12437, d159897, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d12438 q = 1) (hb : d159762 q = 1) : d159898 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d12438, d159898, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d12438, d159898, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h10 p ha hb
theorem andIntro31457 (p : Pattern) (ha : d12442 p = 1) (hb : d159762 p = 1) : d159803 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d159762 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d4819 q = 1) (hb : d159762 q = 1) : d159798 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d4819, d159798, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31417 q ha hb
    | true =>
      simp only [d4819, d159798, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31400 q ha hb
  have h2 (q : Pattern) (ha : d4820 q = 1) (hb : d159762 q = 1) : d159799 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d4820, d159799, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4820, d159799, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d4821 q = 1) (hb : d159762 q = 1) : d159800 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d4821, d159800, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4821, d159800, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d4822 q = 1) (hb : d159762 q = 1) : d159801 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d4822, d159801, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d4822, d159801, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d12441 q = 1) (hb : d159762 q = 1) : d159802 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d12441, d159802, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d12441, d159802, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d12442 q = 1) (hb : d159762 q = 1) : d159803 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d12442, d159803, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d12442, d159803, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro31458 (p : Pattern) (ha : d12448 p = 1) (hb : d159762 p = 1) : d159904 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d159762 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12439 q = 1) (hb : d159762 q = 1) : d159899 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d12439, d159899, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31456 q ha hb
    | true =>
      simp only [d12439, d159899, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d12440 q = 1) (hb : d159762 q = 1) : d159900 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d12440, d159900, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12440, d159900, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d12443 q = 1) (hb : d159762 q = 1) : d159804 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d12443, d159804, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31457 q ha hb
    | true =>
      simp only [d12443, d159804, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d12444 q = 1) (hb : d159762 q = 1) : d159805 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d12444, d159805, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12444, d159805, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d12445 q = 1) (hb : d159762 q = 1) : d159901 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d12445, d159901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d12445, d159901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d12446 q = 1) (hb : d159762 q = 1) : d159902 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d12446, d159902, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d12446, d159902, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d12447 q = 1) (hb : d159762 q = 1) : d159903 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d12447, d159903, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d12447, d159903, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d12448 q = 1) (hb : d159762 q = 1) : d159904 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d12448, d159904, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12448, d159904, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro31459 (p : Pattern) (ha : d12452 p = 1) (hb : d159762 p = 1) : d159809 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d159762 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12443 q = 1) (hb : d159762 q = 1) : d159804 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d12443, d159804, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31457 q ha hb
    | true =>
      simp only [d12443, d159804, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d12444 q = 1) (hb : d159762 q = 1) : d159805 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d12444, d159805, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12444, d159805, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d12449 q = 1) (hb : d159762 q = 1) : d159806 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d12449, d159806, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d12449, d159806, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d12450 q = 1) (hb : d159762 q = 1) : d159807 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d12450, d159807, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d12450, d159807, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d12451 q = 1) (hb : d159762 q = 1) : d159808 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d12451, d159808, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d12451, d159808, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d12452 q = 1) (hb : d159762 q = 1) : d159809 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d12452, d159809, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12452, d159809, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro31460 (p : Pattern) (ha : d12458 p = 1) (hb : d159762 p = 1) : d159977 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d159762 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12453 q = 1) (hb : d159762 q = 1) : d159905 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d12453, d159905, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31458 q ha hb
    | true =>
      simp only [d12453, d159905, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31459 q ha hb
  have h2 (q : Pattern) (ha : d12454 q = 1) (hb : d159762 q = 1) : d159973 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d12454, d159973, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12454, d159973, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d12455 q = 1) (hb : d159762 q = 1) : d159974 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d12455, d159974, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d12455, d159974, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d12456 q = 1) (hb : d159762 q = 1) : d159975 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d12456, d159975, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12456, d159975, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d12457 q = 1) (hb : d159762 q = 1) : d159976 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d12457, d159976, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12457, d159976, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d12458 q = 1) (hb : d159762 q = 1) : d159977 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d12458, d159977, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12458, d159977, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro31461 (p : Pattern) (ha : d12461 p = 1) (hb : d159762 p = 1) : d159920 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d159762 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12439 q = 1) (hb : d159762 q = 1) : d159899 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d12439, d159899, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31456 q ha hb
    | true =>
      simp only [d12439, d159899, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d12440 q = 1) (hb : d159762 q = 1) : d159900 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d12440, d159900, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12440, d159900, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d12443 q = 1) (hb : d159762 q = 1) : d159804 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d12443, d159804, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31457 q ha hb
    | true =>
      simp only [d12443, d159804, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d12444 q = 1) (hb : d159762 q = 1) : d159805 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d12444, d159805, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12444, d159805, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d12445 q = 1) (hb : d159762 q = 1) : d159901 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d12445, d159901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d12445, d159901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d12446 q = 1) (hb : d159762 q = 1) : d159902 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d12446, d159902, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d12446, d159902, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d12447 q = 1) (hb : d159762 q = 1) : d159903 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d12447, d159903, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d12447, d159903, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d12461 q = 1) (hb : d159762 q = 1) : d159920 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d12461, d159920, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d12461, d159920, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro31462 (p : Pattern) (ha : d12462 p = 1) (hb : d159762 p = 1) : d159816 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d159762 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12443 q = 1) (hb : d159762 q = 1) : d159804 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d12443, d159804, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31457 q ha hb
    | true =>
      simp only [d12443, d159804, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d12444 q = 1) (hb : d159762 q = 1) : d159805 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d12444, d159805, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12444, d159805, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d12449 q = 1) (hb : d159762 q = 1) : d159806 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d12449, d159806, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d12449, d159806, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d12450 q = 1) (hb : d159762 q = 1) : d159807 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d12450, d159807, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d12450, d159807, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d12451 q = 1) (hb : d159762 q = 1) : d159808 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d12451, d159808, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d12451, d159808, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d12462 q = 1) (hb : d159762 q = 1) : d159816 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d12462, d159816, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d12462, d159816, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro31463 (p : Pattern) (ha : d12468 p = 1) (hb : d159762 p = 1) : d159984 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d159762 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12453 q = 1) (hb : d159762 q = 1) : d159905 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d12453, d159905, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31458 q ha hb
    | true =>
      simp only [d12453, d159905, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31459 q ha hb
  have h2 (q : Pattern) (ha : d12454 q = 1) (hb : d159762 q = 1) : d159973 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d12454, d159973, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12454, d159973, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d12455 q = 1) (hb : d159762 q = 1) : d159974 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d12455, d159974, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d12455, d159974, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d12456 q = 1) (hb : d159762 q = 1) : d159975 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d12456, d159975, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12456, d159975, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d12457 q = 1) (hb : d159762 q = 1) : d159976 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d12457, d159976, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12457, d159976, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d12463 q = 1) (hb : d159762 q = 1) : d159921 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d12463, d159921, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31461 q ha hb
    | true =>
      simp only [d12463, d159921, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31462 q ha hb
  have h7 (q : Pattern) (ha : d12464 q = 1) (hb : d159762 q = 1) : d159980 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d12464, d159980, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12464, d159980, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d12465 q = 1) (hb : d159762 q = 1) : d159981 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d12465, d159981, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d12465, d159981, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d12466 q = 1) (hb : d159762 q = 1) : d159982 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d12466, d159982, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12466, d159982, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d12467 q = 1) (hb : d159762 q = 1) : d159983 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d12467, d159983, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12467, d159983, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d12468 q = 1) (hb : d159762 q = 1) : d159984 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d12468, d159984, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d12468, d159984, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro31464 (p : Pattern) (ha : d12574 p = 1) (hb : d159762 p = 1) : d160046 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d159762 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12453 q = 1) (hb : d159762 q = 1) : d159905 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d12453, d159905, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31458 q ha hb
    | true =>
      simp only [d12453, d159905, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31459 q ha hb
  have h2 (q : Pattern) (ha : d12454 q = 1) (hb : d159762 q = 1) : d159973 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d12454, d159973, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12454, d159973, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d12455 q = 1) (hb : d159762 q = 1) : d159974 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d12455, d159974, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d12455, d159974, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d12456 q = 1) (hb : d159762 q = 1) : d159975 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d12456, d159975, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12456, d159975, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d12457 q = 1) (hb : d159762 q = 1) : d159976 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d12457, d159976, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12457, d159976, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d12569 q = 1) (hb : d159762 q = 1) : d159810 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d12569, d159810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31459 q ha hb
    | true =>
      simp only [d12569, d159810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d12570 q = 1) (hb : d159762 q = 1) : d159864 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d12570, d159864, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12570, d159864, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d12571 q = 1) (hb : d159762 q = 1) : d159865 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d12571, d159865, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d12571, d159865, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d12572 q = 1) (hb : d159762 q = 1) : d159866 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d12572, d159866, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12572, d159866, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d12573 q = 1) (hb : d159762 q = 1) : d159867 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d12573, d159867, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12573, d159867, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d12574 q = 1) (hb : d159762 q = 1) : d160046 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d12574, d160046, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d12574, d160046, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro31465 (p : Pattern) (ha : d12580 p = 1) (hb : d159762 p = 1) : d159875 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d159762 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12569 q = 1) (hb : d159762 q = 1) : d159810 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d12569, d159810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31459 q ha hb
    | true =>
      simp only [d12569, d159810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d12570 q = 1) (hb : d159762 q = 1) : d159864 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d12570, d159864, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12570, d159864, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d12571 q = 1) (hb : d159762 q = 1) : d159865 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d12571, d159865, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d12571, d159865, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d12572 q = 1) (hb : d159762 q = 1) : d159866 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d12572, d159866, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12572, d159866, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d12573 q = 1) (hb : d159762 q = 1) : d159867 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d12573, d159867, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12573, d159867, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d12575 q = 1) (hb : d159762 q = 1) : d159817 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d12575, d159817, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31462 q ha hb
    | true =>
      simp only [d12575, d159817, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d12576 q = 1) (hb : d159762 q = 1) : d159871 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d12576, d159871, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12576, d159871, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d12577 q = 1) (hb : d159762 q = 1) : d159872 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d12577, d159872, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d12577, d159872, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d12578 q = 1) (hb : d159762 q = 1) : d159873 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d12578, d159873, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12578, d159873, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d12579 q = 1) (hb : d159762 q = 1) : d159874 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d12579, d159874, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12579, d159874, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d12580 q = 1) (hb : d159762 q = 1) : d159875 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d12580, d159875, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d12580, d159875, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro31466 (p : Pattern) (ha : d12589 p = 1) (hb : d159762 p = 1) : d160055 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d159762 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12575 q = 1) (hb : d159762 q = 1) : d159817 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d12575, d159817, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31462 q ha hb
    | true =>
      simp only [d12575, d159817, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d12576 q = 1) (hb : d159762 q = 1) : d159871 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d12576, d159871, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12576, d159871, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d12577 q = 1) (hb : d159762 q = 1) : d159872 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d12577, d159872, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d12577, d159872, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d12578 q = 1) (hb : d159762 q = 1) : d159873 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d12578, d159873, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12578, d159873, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d12579 q = 1) (hb : d159762 q = 1) : d159874 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d12579, d159874, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12579, d159874, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d12589 q = 1) (hb : d159762 q = 1) : d160055 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d12589, d160055, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12589, d160055, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro31467 (p : Pattern) (ha : d12622 p = 1) (hb : d159762 p = 1) : d159840 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d159762 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d6079 q = 1) (hb : d159762 q = 1) : d159835 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d6079, d159835, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31426 q ha hb
    | true =>
      simp only [d6079, d159835, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31407 q ha hb
  have h2 (q : Pattern) (ha : d6080 q = 1) (hb : d159762 q = 1) : d159836 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d6080, d159836, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6080, d159836, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d6081 q = 1) (hb : d159762 q = 1) : d159837 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d6081, d159837, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6081, d159837, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d6082 q = 1) (hb : d159762 q = 1) : d159838 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d6082, d159838, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d6082, d159838, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d12621 q = 1) (hb : d159762 q = 1) : d159839 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d12621, d159839, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d12621, d159839, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d12622 q = 1) (hb : d159762 q = 1) : d159840 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d12622, d159840, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d12622, d159840, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro31468 (p : Pattern) (ha : d12668 p = 1) (hb : d159762 p = 1) : d159846 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d159762 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12623 q = 1) (hb : d159762 q = 1) : d159841 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d12623, d159841, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31467 q ha hb
    | true =>
      simp only [d12623, d159841, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d12624 q = 1) (hb : d159762 q = 1) : d159842 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d12624, d159842, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12624, d159842, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d12665 q = 1) (hb : d159762 q = 1) : d159843 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d12665, d159843, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d12665, d159843, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d12666 q = 1) (hb : d159762 q = 1) : d159844 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d12666, d159844, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d12666, d159844, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d12667 q = 1) (hb : d159762 q = 1) : d159845 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d12667, d159845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d12667, d159845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d12668 q = 1) (hb : d159762 q = 1) : d159846 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d12668, d159846, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d12668, d159846, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro31469 (p : Pattern) (ha : d12674 p = 1) (hb : d159762 p = 1) : d160092 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d159762 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12669 q = 1) (hb : d159762 q = 1) : d159847 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d12669, d159847, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31468 q ha hb
    | true =>
      simp only [d12669, d159847, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d12670 q = 1) (hb : d159762 q = 1) : d160088 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d12670, d160088, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12670, d160088, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d12671 q = 1) (hb : d159762 q = 1) : d160089 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d12671, d160089, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d12671, d160089, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d12672 q = 1) (hb : d159762 q = 1) : d160090 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d12672, d160090, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12672, d160090, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d12673 q = 1) (hb : d159762 q = 1) : d160091 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d12673, d160091, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12673, d160091, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d12674 q = 1) (hb : d159762 q = 1) : d160092 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d12674, d160092, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12674, d160092, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro31470 (p : Pattern) (ha : d12473 p = 1) (hb : d159762 p = 1) : d159989 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d159762 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12439 q = 1) (hb : d159762 q = 1) : d159899 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d12439, d159899, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31456 q ha hb
    | true =>
      simp only [d12439, d159899, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d12440 q = 1) (hb : d159762 q = 1) : d159900 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d12440, d159900, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12440, d159900, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d12443 q = 1) (hb : d159762 q = 1) : d159804 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d12443, d159804, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31457 q ha hb
    | true =>
      simp only [d12443, d159804, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d12444 q = 1) (hb : d159762 q = 1) : d159805 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d12444, d159805, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12444, d159805, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d12445 q = 1) (hb : d159762 q = 1) : d159901 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d12445, d159901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d12445, d159901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d12446 q = 1) (hb : d159762 q = 1) : d159902 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d12446, d159902, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d12446, d159902, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d12472 q = 1) (hb : d159762 q = 1) : d159988 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d12472, d159988, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12472, d159988, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d12473 q = 1) (hb : d159762 q = 1) : d159989 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d12473, d159989, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12473, d159989, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro31471 (p : Pattern) (ha : d12475 p = 1) (hb : d159762 p = 1) : d159880 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d159762 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12443 q = 1) (hb : d159762 q = 1) : d159804 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d12443, d159804, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31457 q ha hb
    | true =>
      simp only [d12443, d159804, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d12444 q = 1) (hb : d159762 q = 1) : d159805 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d12444, d159805, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12444, d159805, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d12449 q = 1) (hb : d159762 q = 1) : d159806 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d12449, d159806, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d12449, d159806, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d12450 q = 1) (hb : d159762 q = 1) : d159807 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d12450, d159807, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d12450, d159807, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d12474 q = 1) (hb : d159762 q = 1) : d159879 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d12474, d159879, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12474, d159879, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d12475 q = 1) (hb : d159762 q = 1) : d159880 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d12475, d159880, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12475, d159880, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro31472 (p : Pattern) (ha : d12482 p = 1) (hb : d159762 p = 1) : d159996 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d159762 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12439 q = 1) (hb : d159762 q = 1) : d159899 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d12439, d159899, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31456 q ha hb
    | true =>
      simp only [d12439, d159899, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d12440 q = 1) (hb : d159762 q = 1) : d159900 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d12440, d159900, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12440, d159900, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d12443 q = 1) (hb : d159762 q = 1) : d159804 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d12443, d159804, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31457 q ha hb
    | true =>
      simp only [d12443, d159804, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d12444 q = 1) (hb : d159762 q = 1) : d159805 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d12444, d159805, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12444, d159805, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d12445 q = 1) (hb : d159762 q = 1) : d159901 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d12445, d159901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d12445, d159901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d12480 q = 1) (hb : d159762 q = 1) : d159994 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d12480, d159994, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12480, d159994, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d12481 q = 1) (hb : d159762 q = 1) : d159995 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d12481, d159995, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d12481, d159995, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d12482 q = 1) (hb : d159762 q = 1) : d159996 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d12482, d159996, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12482, d159996, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro31473 (p : Pattern) (ha : d12485 p = 1) (hb : d159762 p = 1) : d159887 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d159762 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12443 q = 1) (hb : d159762 q = 1) : d159804 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d12443, d159804, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31457 q ha hb
    | true =>
      simp only [d12443, d159804, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d12444 q = 1) (hb : d159762 q = 1) : d159805 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d12444, d159805, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12444, d159805, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d12449 q = 1) (hb : d159762 q = 1) : d159806 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d12449, d159806, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d12449, d159806, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d12483 q = 1) (hb : d159762 q = 1) : d159885 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d12483, d159885, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12483, d159885, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d12484 q = 1) (hb : d159762 q = 1) : d159886 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d12484, d159886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d12484, d159886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d12485 q = 1) (hb : d159762 q = 1) : d159887 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d12485, d159887, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12485, d159887, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro31474 (p : Pattern) (ha : d12489 p = 1) (hb : d159762 p = 1) : d160001 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d546 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d322 q = 1) (hb : d100904 q = 1) : d322 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d547 q = 1) (hb : d159761 q = 1) : d160000 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d547, d159761, d160000, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d547, d159761, d160000, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d12489 q = 1) (hb : d159762 q = 1) : d160001 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d12489, d159762, d160001, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d12489, d159762, d160001, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  exact h4 p ha hb
theorem andIntro31475 (p : Pattern) (ha : d12496 p = 1) (hb : d159762 p = 1) : d159797 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d12494 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d28 q = 1) (hb : d100904 q = 1) : d28 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d12495 q = 1) (hb : d159761 q = 1) : d159796 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d12495, d159761, d159796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d12495, d159761, d159796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d12496 q = 1) (hb : d159762 q = 1) : d159797 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d12496, d159762, d159797, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d12496, d159762, d159797, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  exact h4 p ha hb
theorem andIntro31476 (p : Pattern) (ha : d12502 p = 1) (hb : d159762 p = 1) : d160007 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d159762 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12490 q = 1) (hb : d159762 q = 1) : d160002 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d12490, d160002, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31474 q ha hb
    | true =>
      simp only [d12490, d160002, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31438 q ha hb
  have h2 (q : Pattern) (ha : d12491 q = 1) (hb : d159762 q = 1) : d160003 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d12491, d160003, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12491, d160003, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d12492 q = 1) (hb : d159762 q = 1) : d160004 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d12492, d160004, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12492, d160004, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d12497 q = 1) (hb : d159762 q = 1) : d159893 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d12497, d159893, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31438 q ha hb
    | true =>
      simp only [d12497, d159893, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31475 q ha hb
  have h5 (q : Pattern) (ha : d12498 q = 1) (hb : d159762 q = 1) : d159894 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d12498, d159894, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12498, d159894, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d12499 q = 1) (hb : d159762 q = 1) : d159895 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d12499, d159895, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12499, d159895, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d12500 q = 1) (hb : d159762 q = 1) : d160005 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d12500, d160005, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d12500, d160005, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d12313 q = 1) (hb : d159762 q = 1) : d159893 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d12313, d159893, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31438 q ha hb
    | true =>
      simp only [d12313, d159893, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31417 q ha hb
  have h9 (q : Pattern) (ha : d12314 q = 1) (hb : d159762 q = 1) : d159894 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d12314, d159894, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12314, d159894, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d12315 q = 1) (hb : d159762 q = 1) : d159895 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d12315, d159895, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12315, d159895, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d4819 q = 1) (hb : d159762 q = 1) : d159798 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d4819, d159798, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31417 q ha hb
    | true =>
      simp only [d4819, d159798, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31400 q ha hb
  have h12 (q : Pattern) (ha : d4820 q = 1) (hb : d159762 q = 1) : d159799 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d4820, d159799, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4820, d159799, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d4821 q = 1) (hb : d159762 q = 1) : d159800 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d4821, d159800, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4821, d159800, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d12316 q = 1) (hb : d159762 q = 1) : d159896 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d12316, d159896, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d12316, d159896, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d12501 q = 1) (hb : d159762 q = 1) : d160006 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d12501, d160006, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d12501, d160006, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d12502 q = 1) (hb : d159762 q = 1) : d160007 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d12502, d160007, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d12502, d160007, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h16 p ha hb
theorem andIntro31477 (p : Pattern) (ha : d12508 p = 1) (hb : d159762 p = 1) : d160013 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d159762 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12503 q = 1) (hb : d159762 q = 1) : d160008 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d12503, d160008, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31476 q ha hb
    | true =>
      simp only [d12503, d160008, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d12504 q = 1) (hb : d159762 q = 1) : d160009 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d12504, d160009, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12504, d160009, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d12439 q = 1) (hb : d159762 q = 1) : d159899 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d12439, d159899, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31456 q ha hb
    | true =>
      simp only [d12439, d159899, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d12440 q = 1) (hb : d159762 q = 1) : d159900 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d12440, d159900, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12440, d159900, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d12505 q = 1) (hb : d159762 q = 1) : d160010 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d12505, d160010, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d12505, d160010, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d12506 q = 1) (hb : d159762 q = 1) : d160011 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d12506, d160011, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d12506, d160011, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d12507 q = 1) (hb : d159762 q = 1) : d160012 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d12507, d160012, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d12507, d160012, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d12508 q = 1) (hb : d159762 q = 1) : d160013 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d12508, d160013, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12508, d160013, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro31478 (p : Pattern) (ha : d12537 p = 1) (hb : d159762 p = 1) : d160019 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d159762 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12439 q = 1) (hb : d159762 q = 1) : d159899 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d12439, d159899, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31456 q ha hb
    | true =>
      simp only [d12439, d159899, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d12440 q = 1) (hb : d159762 q = 1) : d159900 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d12440, d159900, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12440, d159900, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d12534 q = 1) (hb : d159762 q = 1) : d160016 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d12534, d160016, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d12534, d160016, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d12535 q = 1) (hb : d159762 q = 1) : d160017 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d12535, d160017, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d12535, d160017, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d12536 q = 1) (hb : d159762 q = 1) : d160018 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d12536, d160018, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d12536, d160018, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d12537 q = 1) (hb : d159762 q = 1) : d160019 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d12537, d160019, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12537, d160019, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro31479 (p : Pattern) (ha : d115319 p = 1) (hb : d159762 p = 1) : d160025 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d159762 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12476 q = 1) (hb : d159762 q = 1) : d159990 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d12476, d159990, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31470 q ha hb
    | true =>
      simp only [d12476, d159990, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31471 q ha hb
  have h2 (q : Pattern) (ha : d12477 q = 1) (hb : d159762 q = 1) : d159991 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d12477, d159991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12477, d159991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d12478 q = 1) (hb : d159762 q = 1) : d159992 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d12478, d159992, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d12478, d159992, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d12479 q = 1) (hb : d159762 q = 1) : d159993 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d12479, d159993, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12479, d159993, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d12486 q = 1) (hb : d159762 q = 1) : d159997 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d12486, d159997, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31472 q ha hb
    | true =>
      simp only [d12486, d159997, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31473 q ha hb
  have h6 (q : Pattern) (ha : d12487 q = 1) (hb : d159762 q = 1) : d159998 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d12487, d159998, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12487, d159998, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d12488 q = 1) (hb : d159762 q = 1) : d159999 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d12488, d159999, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d12488, d159999, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d12509 q = 1) (hb : d159762 q = 1) : d160014 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d12509, d160014, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31477 q ha hb
    | true =>
      simp only [d12509, d160014, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31458 q ha hb
  have h9 (q : Pattern) (ha : d115315 q = 1) (hb : d159762 q = 1) : d160015 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d115315, d160015, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d115315, d160015, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d12538 q = 1) (hb : d159762 q = 1) : d160020 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d12538, d160020, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31478 q ha hb
    | true =>
      simp only [d12538, d160020, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d12539 q = 1) (hb : d159762 q = 1) : d160021 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d12539, d160021, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d12539, d160021, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d115316 q = 1) (hb : d159762 q = 1) : d160022 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d115316, d160022, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d115316, d160022, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d115317 q = 1) (hb : d159762 q = 1) : d160023 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d115317, d160023, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d115317, d160023, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d115318 q = 1) (hb : d159762 q = 1) : d160024 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d115318, d160024, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d115318, d160024, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d115319 q = 1) (hb : d159762 q = 1) : d160025 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d115319, d160025, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d115319, d160025, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro31480 (p : Pattern) (ha : d12544 p = 1) (hb : d159762 p = 1) : d160026 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d159762 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12439 q = 1) (hb : d159762 q = 1) : d159899 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d12439, d159899, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31456 q ha hb
    | true =>
      simp only [d12439, d159899, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d12440 q = 1) (hb : d159762 q = 1) : d159900 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d12440, d159900, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12440, d159900, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d12443 q = 1) (hb : d159762 q = 1) : d159804 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d12443, d159804, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31457 q ha hb
    | true =>
      simp only [d12443, d159804, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d12444 q = 1) (hb : d159762 q = 1) : d159805 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d12444, d159805, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12444, d159805, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d12445 q = 1) (hb : d159762 q = 1) : d159901 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d12445, d159901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d12445, d159901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d12446 q = 1) (hb : d159762 q = 1) : d159902 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d12446, d159902, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d12446, d159902, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d12472 q = 1) (hb : d159762 q = 1) : d159988 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d12472, d159988, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12472, d159988, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d12544 q = 1) (hb : d159762 q = 1) : d160026 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d12544, d160026, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d12544, d160026, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro31481 (p : Pattern) (ha : d12545 p = 1) (hb : d159762 p = 1) : d159911 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d159762 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12443 q = 1) (hb : d159762 q = 1) : d159804 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d12443, d159804, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31457 q ha hb
    | true =>
      simp only [d12443, d159804, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d12444 q = 1) (hb : d159762 q = 1) : d159805 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d12444, d159805, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12444, d159805, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d12449 q = 1) (hb : d159762 q = 1) : d159806 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d12449, d159806, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d12449, d159806, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d12450 q = 1) (hb : d159762 q = 1) : d159807 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d12450, d159807, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d12450, d159807, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d12474 q = 1) (hb : d159762 q = 1) : d159879 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d12474, d159879, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12474, d159879, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d12545 q = 1) (hb : d159762 q = 1) : d159911 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d12545, d159911, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d12545, d159911, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro31482 (p : Pattern) (ha : d12550 p = 1) (hb : d159762 p = 1) : d160031 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d159762 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12439 q = 1) (hb : d159762 q = 1) : d159899 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d12439, d159899, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31456 q ha hb
    | true =>
      simp only [d12439, d159899, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d12440 q = 1) (hb : d159762 q = 1) : d159900 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d12440, d159900, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12440, d159900, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d12443 q = 1) (hb : d159762 q = 1) : d159804 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d12443, d159804, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31457 q ha hb
    | true =>
      simp only [d12443, d159804, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d12444 q = 1) (hb : d159762 q = 1) : d159805 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d12444, d159805, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12444, d159805, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d12445 q = 1) (hb : d159762 q = 1) : d159901 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d12445, d159901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d12445, d159901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d12480 q = 1) (hb : d159762 q = 1) : d159994 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d12480, d159994, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12480, d159994, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d12481 q = 1) (hb : d159762 q = 1) : d159995 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d12481, d159995, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d12481, d159995, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d12550 q = 1) (hb : d159762 q = 1) : d160031 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d12550, d160031, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d12550, d160031, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro31483 (p : Pattern) (ha : d12551 p = 1) (hb : d159762 p = 1) : d159916 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d159762 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12443 q = 1) (hb : d159762 q = 1) : d159804 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d12443, d159804, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31457 q ha hb
    | true =>
      simp only [d12443, d159804, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d12444 q = 1) (hb : d159762 q = 1) : d159805 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d12444, d159805, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12444, d159805, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d12449 q = 1) (hb : d159762 q = 1) : d159806 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d12449, d159806, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d12449, d159806, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d12483 q = 1) (hb : d159762 q = 1) : d159885 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d12483, d159885, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12483, d159885, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d12484 q = 1) (hb : d159762 q = 1) : d159886 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d12484, d159886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d12484, d159886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d12551 q = 1) (hb : d159762 q = 1) : d159916 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d12551, d159916, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d12551, d159916, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro31484 (p : Pattern) (ha : d12555 p = 1) (hb : d159762 p = 1) : d160035 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d159762 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12503 q = 1) (hb : d159762 q = 1) : d160008 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d12503, d160008, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31476 q ha hb
    | true =>
      simp only [d12503, d160008, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d12504 q = 1) (hb : d159762 q = 1) : d160009 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d12504, d160009, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12504, d160009, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d12439 q = 1) (hb : d159762 q = 1) : d159899 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d12439, d159899, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31456 q ha hb
    | true =>
      simp only [d12439, d159899, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d12440 q = 1) (hb : d159762 q = 1) : d159900 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d12440, d159900, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12440, d159900, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d12505 q = 1) (hb : d159762 q = 1) : d160010 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d12505, d160010, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d12505, d160010, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d12506 q = 1) (hb : d159762 q = 1) : d160011 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d12506, d160011, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d12506, d160011, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d12507 q = 1) (hb : d159762 q = 1) : d160012 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d12507, d160012, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d12507, d160012, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d12555 q = 1) (hb : d159762 q = 1) : d160035 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d12555, d160035, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d12555, d160035, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro31485 (p : Pattern) (ha : d12561 p = 1) (hb : d159762 p = 1) : d160038 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d159762 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12439 q = 1) (hb : d159762 q = 1) : d159899 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d12439, d159899, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31456 q ha hb
    | true =>
      simp only [d12439, d159899, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d12440 q = 1) (hb : d159762 q = 1) : d159900 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d12440, d159900, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12440, d159900, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d12534 q = 1) (hb : d159762 q = 1) : d160016 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d12534, d160016, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d12534, d160016, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d12535 q = 1) (hb : d159762 q = 1) : d160017 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d12535, d160017, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d12535, d160017, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d12536 q = 1) (hb : d159762 q = 1) : d160018 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d12536, d160018, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d12536, d160018, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d12561 q = 1) (hb : d159762 q = 1) : d160038 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d12561, d160038, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d12561, d160038, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro31486 (p : Pattern) (ha : d115324 p = 1) (hb : d159762 p = 1) : d160044 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d159762 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12476 q = 1) (hb : d159762 q = 1) : d159990 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d12476, d159990, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31470 q ha hb
    | true =>
      simp only [d12476, d159990, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31471 q ha hb
  have h2 (q : Pattern) (ha : d12477 q = 1) (hb : d159762 q = 1) : d159991 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d12477, d159991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12477, d159991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d12478 q = 1) (hb : d159762 q = 1) : d159992 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d12478, d159992, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d12478, d159992, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d12479 q = 1) (hb : d159762 q = 1) : d159993 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d12479, d159993, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12479, d159993, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d12486 q = 1) (hb : d159762 q = 1) : d159997 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d12486, d159997, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31472 q ha hb
    | true =>
      simp only [d12486, d159997, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31473 q ha hb
  have h6 (q : Pattern) (ha : d12487 q = 1) (hb : d159762 q = 1) : d159998 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d12487, d159998, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12487, d159998, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d12488 q = 1) (hb : d159762 q = 1) : d159999 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d12488, d159999, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d12488, d159999, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d12509 q = 1) (hb : d159762 q = 1) : d160014 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d12509, d160014, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31477 q ha hb
    | true =>
      simp only [d12509, d160014, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31458 q ha hb
  have h9 (q : Pattern) (ha : d115315 q = 1) (hb : d159762 q = 1) : d160015 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d115315, d160015, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d115315, d160015, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d12538 q = 1) (hb : d159762 q = 1) : d160020 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d12538, d160020, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31478 q ha hb
    | true =>
      simp only [d12538, d160020, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d12539 q = 1) (hb : d159762 q = 1) : d160021 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d12539, d160021, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d12539, d160021, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d115316 q = 1) (hb : d159762 q = 1) : d160022 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d115316, d160022, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d115316, d160022, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d115317 q = 1) (hb : d159762 q = 1) : d160023 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d115317, d160023, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d115317, d160023, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d115318 q = 1) (hb : d159762 q = 1) : d160024 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d115318, d160024, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d115318, d160024, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d12546 q = 1) (hb : d159762 q = 1) : d160027 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d12546, d160027, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31480 q ha hb
    | true =>
      simp only [d12546, d160027, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31481 q ha hb
  have h16 (q : Pattern) (ha : d12547 q = 1) (hb : d159762 q = 1) : d160028 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d12547, d160028, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12547, d160028, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d12548 q = 1) (hb : d159762 q = 1) : d160029 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d12548, d160029, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d12548, d160029, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h18 (q : Pattern) (ha : d12549 q = 1) (hb : d159762 q = 1) : d160030 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d12549, d160030, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12549, d160030, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d12552 q = 1) (hb : d159762 q = 1) : d160032 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d12552, d160032, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31482 q ha hb
    | true =>
      simp only [d12552, d160032, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31483 q ha hb
  have h20 (q : Pattern) (ha : d12553 q = 1) (hb : d159762 q = 1) : d160033 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d12553, d160033, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12553, d160033, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
  have h21 (q : Pattern) (ha : d12554 q = 1) (hb : d159762 q = 1) : d160034 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d12554, d160034, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d12554, d160034, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h22 (q : Pattern) (ha : d12556 q = 1) (hb : d159762 q = 1) : d160036 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d12556, d160036, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31484 q ha hb
    | true =>
      simp only [d12556, d160036, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31461 q ha hb
  have h23 (q : Pattern) (ha : d115320 q = 1) (hb : d159762 q = 1) : d160037 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d115320, d160037, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
    | true =>
      simp only [d115320, d160037, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h24 (q : Pattern) (ha : d12562 q = 1) (hb : d159762 q = 1) : d160039 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d12562, d160039, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31485 q ha hb
    | true =>
      simp only [d12562, d160039, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h25 (q : Pattern) (ha : d12563 q = 1) (hb : d159762 q = 1) : d160040 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d12563, d160040, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q ha hb
    | true =>
      simp only [d12563, d160040, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h26 (q : Pattern) (ha : d115321 q = 1) (hb : d159762 q = 1) : d160041 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d115321, d160041, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
    | true =>
      simp only [d115321, d160041, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q ha hb
  have h27 (q : Pattern) (ha : d115322 q = 1) (hb : d159762 q = 1) : d160042 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d115322, d160042, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d115322, d160042, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h26 q ha hb
  have h28 (q : Pattern) (ha : d115323 q = 1) (hb : d159762 q = 1) : d160043 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d115323, d160043, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d115323, d160043, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h27 q ha hb
  have h29 (q : Pattern) (ha : d115324 q = 1) (hb : d159762 q = 1) : d160044 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d115324, d160044, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d115324, d160044, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h28 q ha hb
  exact h29 p ha hb
theorem andIntro31487 (p : Pattern) (ha : d115331 p = 1) (hb : d159762 p = 1) : d160053 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d159762 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12556 q = 1) (hb : d159762 q = 1) : d160036 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d12556, d160036, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31484 q ha hb
    | true =>
      simp only [d12556, d160036, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31461 q ha hb
  have h2 (q : Pattern) (ha : d115320 q = 1) (hb : d159762 q = 1) : d160037 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d115320, d160037, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d115320, d160037, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d12562 q = 1) (hb : d159762 q = 1) : d160039 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d12562, d160039, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31485 q ha hb
    | true =>
      simp only [d12562, d160039, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d12563 q = 1) (hb : d159762 q = 1) : d160040 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d12563, d160040, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d12563, d160040, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d115321 q = 1) (hb : d159762 q = 1) : d160041 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d115321, d160041, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d115321, d160041, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d115329 q = 1) (hb : d159762 q = 1) : d160051 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d115329, d160051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d115329, d160051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d115330 q = 1) (hb : d159762 q = 1) : d160052 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d115330, d160052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d115330, d160052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d115331 q = 1) (hb : d159762 q = 1) : d160053 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d115331, d160053, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d115331, d160053, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro31488 (p : Pattern) (ha : d12595 p = 1) (hb : d159762 p = 1) : d160062 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d662 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d415 q = 1) (hb : d100904 q = 1) : d415 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d663 q = 1) (hb : d159761 q = 1) : d160061 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d663, d159761, d160061, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d663, d159761, d160061, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d12595 q = 1) (hb : d159762 q = 1) : d160062 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d12595, d159762, d160062, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d12595, d159762, d160062, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  exact h4 p ha hb
theorem andIntro31489 (p : Pattern) (ha : d12604 p = 1) (hb : d159762 p = 1) : d159834 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d12602 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d69 q = 1) (hb : d100904 q = 1) : d69 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d12603 q = 1) (hb : d159761 q = 1) : d159833 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d12603, d159761, d159833, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d12603, d159761, d159833, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d12604 q = 1) (hb : d159762 q = 1) : d159834 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d12604, d159762, d159834, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d12604, d159762, d159834, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  exact h4 p ha hb
theorem andIntro31490 (p : Pattern) (ha : d12610 p = 1) (hb : d159762 p = 1) : d160068 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d159762 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12596 q = 1) (hb : d159762 q = 1) : d160063 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d12596, d160063, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31488 q ha hb
    | true =>
      simp only [d12596, d160063, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31449 q ha hb
  have h2 (q : Pattern) (ha : d12597 q = 1) (hb : d159762 q = 1) : d160064 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d12597, d160064, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12597, d160064, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d12598 q = 1) (hb : d159762 q = 1) : d160065 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d12598, d160065, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12598, d160065, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d12605 q = 1) (hb : d159762 q = 1) : d159943 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d12605, d159943, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31449 q ha hb
    | true =>
      simp only [d12605, d159943, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31489 q ha hb
  have h5 (q : Pattern) (ha : d12606 q = 1) (hb : d159762 q = 1) : d159944 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d12606, d159944, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12606, d159944, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d12607 q = 1) (hb : d159762 q = 1) : d159945 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d12607, d159945, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12607, d159945, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d12608 q = 1) (hb : d159762 q = 1) : d160066 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d12608, d160066, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d12608, d160066, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d12387 q = 1) (hb : d159762 q = 1) : d159943 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d12387, d159943, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31449 q ha hb
    | true =>
      simp only [d12387, d159943, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31426 q ha hb
  have h9 (q : Pattern) (ha : d12388 q = 1) (hb : d159762 q = 1) : d159944 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d12388, d159944, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12388, d159944, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d12389 q = 1) (hb : d159762 q = 1) : d159945 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d12389, d159945, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12389, d159945, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d6079 q = 1) (hb : d159762 q = 1) : d159835 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d6079, d159835, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31426 q ha hb
    | true =>
      simp only [d6079, d159835, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31407 q ha hb
  have h12 (q : Pattern) (ha : d6080 q = 1) (hb : d159762 q = 1) : d159836 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d6080, d159836, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6080, d159836, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d6081 q = 1) (hb : d159762 q = 1) : d159837 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d6081, d159837, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6081, d159837, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d12390 q = 1) (hb : d159762 q = 1) : d159946 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d12390, d159946, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d12390, d159946, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d12609 q = 1) (hb : d159762 q = 1) : d160067 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d12609, d160067, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d12609, d160067, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d12610 q = 1) (hb : d159762 q = 1) : d160068 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d12610, d160068, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d12610, d160068, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h16 p ha hb
theorem andIntro31491 (p : Pattern) (ha : d12614 p = 1) (hb : d159762 p = 1) : d159948 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d159762 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12387 q = 1) (hb : d159762 q = 1) : d159943 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d12387, d159943, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31449 q ha hb
    | true =>
      simp only [d12387, d159943, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31426 q ha hb
  have h2 (q : Pattern) (ha : d12388 q = 1) (hb : d159762 q = 1) : d159944 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d12388, d159944, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12388, d159944, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d12389 q = 1) (hb : d159762 q = 1) : d159945 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d12389, d159945, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12389, d159945, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d6079 q = 1) (hb : d159762 q = 1) : d159835 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d6079, d159835, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31426 q ha hb
    | true =>
      simp only [d6079, d159835, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31407 q ha hb
  have h5 (q : Pattern) (ha : d6080 q = 1) (hb : d159762 q = 1) : d159836 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d6080, d159836, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6080, d159836, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d6081 q = 1) (hb : d159762 q = 1) : d159837 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d6081, d159837, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6081, d159837, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d12390 q = 1) (hb : d159762 q = 1) : d159946 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d12390, d159946, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d12390, d159946, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d6082 q = 1) (hb : d159762 q = 1) : d159838 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d6082, d159838, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d6082, d159838, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d12613 q = 1) (hb : d159762 q = 1) : d159947 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d12613, d159947, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d12613, d159947, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d12614 q = 1) (hb : d159762 q = 1) : d159948 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d12614, d159948, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d12614, d159948, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h10 p ha hb
theorem andIntro31492 (p : Pattern) (ha : d12620 p = 1) (hb : d159762 p = 1) : d160074 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d159762 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12611 q = 1) (hb : d159762 q = 1) : d160069 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d12611, d160069, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31490 q ha hb
    | true =>
      simp only [d12611, d160069, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d12612 q = 1) (hb : d159762 q = 1) : d160070 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d12612, d160070, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12612, d160070, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d12615 q = 1) (hb : d159762 q = 1) : d159949 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d12615, d159949, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31491 q ha hb
    | true =>
      simp only [d12615, d159949, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d12616 q = 1) (hb : d159762 q = 1) : d159950 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d12616, d159950, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12616, d159950, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d12617 q = 1) (hb : d159762 q = 1) : d160071 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d12617, d160071, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d12617, d160071, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d12618 q = 1) (hb : d159762 q = 1) : d160072 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d12618, d160072, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d12618, d160072, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d12619 q = 1) (hb : d159762 q = 1) : d160073 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d12619, d160073, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d12619, d160073, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d12620 q = 1) (hb : d159762 q = 1) : d160074 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d12620, d160074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d12620, d160074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro31493 (p : Pattern) (ha : d12628 p = 1) (hb : d159762 p = 1) : d159954 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d159762 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12615 q = 1) (hb : d159762 q = 1) : d159949 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d12615, d159949, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31491 q ha hb
    | true =>
      simp only [d12615, d159949, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d12616 q = 1) (hb : d159762 q = 1) : d159950 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d12616, d159950, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12616, d159950, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d12623 q = 1) (hb : d159762 q = 1) : d159841 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d12623, d159841, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31467 q ha hb
    | true =>
      simp only [d12623, d159841, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d12624 q = 1) (hb : d159762 q = 1) : d159842 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d12624, d159842, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12624, d159842, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d12625 q = 1) (hb : d159762 q = 1) : d159951 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d12625, d159951, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d12625, d159951, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d12626 q = 1) (hb : d159762 q = 1) : d159952 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d12626, d159952, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d12626, d159952, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d12627 q = 1) (hb : d159762 q = 1) : d159953 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d12627, d159953, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d12627, d159953, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d12628 q = 1) (hb : d159762 q = 1) : d159954 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d12628, d159954, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d12628, d159954, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro31494 (p : Pattern) (ha : d12657 p = 1) (hb : d159762 p = 1) : d160080 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d159762 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12615 q = 1) (hb : d159762 q = 1) : d159949 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d12615, d159949, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31491 q ha hb
    | true =>
      simp only [d12615, d159949, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d12616 q = 1) (hb : d159762 q = 1) : d159950 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d12616, d159950, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12616, d159950, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d12654 q = 1) (hb : d159762 q = 1) : d160077 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d12654, d160077, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d12654, d160077, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d12655 q = 1) (hb : d159762 q = 1) : d160078 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d12655, d160078, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d12655, d160078, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d12656 q = 1) (hb : d159762 q = 1) : d160079 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d12656, d160079, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d12656, d160079, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d12657 q = 1) (hb : d159762 q = 1) : d160080 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d12657, d160080, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d12657, d160080, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro31495 (p : Pattern) (ha : d115341 p = 1) (hb : d159762 p = 1) : d160086 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d159762 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12629 q = 1) (hb : d159762 q = 1) : d160075 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d12629, d160075, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31492 q ha hb
    | true =>
      simp only [d12629, d160075, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31493 q ha hb
  have h2 (q : Pattern) (ha : d115337 q = 1) (hb : d159762 q = 1) : d160076 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d115337, d160076, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d115337, d160076, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d12658 q = 1) (hb : d159762 q = 1) : d160081 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d12658, d160081, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31494 q ha hb
    | true =>
      simp only [d12658, d160081, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d12659 q = 1) (hb : d159762 q = 1) : d160082 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d12659, d160082, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d12659, d160082, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d115338 q = 1) (hb : d159762 q = 1) : d160083 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d115338, d160083, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d115338, d160083, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d115339 q = 1) (hb : d159762 q = 1) : d160084 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d115339, d160084, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d115339, d160084, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d115340 q = 1) (hb : d159762 q = 1) : d160085 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d115340, d160085, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d115340, d160085, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d115341 q = 1) (hb : d159762 q = 1) : d160086 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d115341, d160086, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d115341, d160086, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro31496 (p : Pattern) (ha : d115347 p = 1) (hb : d159762 p = 1) : d160098 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d159762 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12459 q = 1) (hb : d159762 q = 1) : d159978 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d12459, d159978, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12459, d159978, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31460 q ha hb
  have h2 (q : Pattern) (ha : d12460 q = 1) (hb : d159762 q = 1) : d159979 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d12460, d159979, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d12460, d159979, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d12469 q = 1) (hb : d159762 q = 1) : d159985 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d12469, d159985, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31460 q ha hb
    | true =>
      simp only [d12469, d159985, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31463 q ha hb
  have h4 (q : Pattern) (ha : d12470 q = 1) (hb : d159762 q = 1) : d159986 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d12470, d159986, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d12470, d159986, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d12471 q = 1) (hb : d159762 q = 1) : d159987 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d12471, d159987, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d12471, d159987, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d115325 q = 1) (hb : d159762 q = 1) : d160045 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d115325, d160045, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31479 q ha hb
    | true =>
      simp only [d115325, d160045, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31486 q ha hb
  have h7 (q : Pattern) (ha : d12581 q = 1) (hb : d159762 q = 1) : d160047 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d12581, d160047, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31464 q ha hb
    | true =>
      simp only [d12581, d160047, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31465 q ha hb
  have h8 (q : Pattern) (ha : d115326 q = 1) (hb : d159762 q = 1) : d160048 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d115326, d160048, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d115326, d160048, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d115327 q = 1) (hb : d159762 q = 1) : d160049 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d115327, d160049, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d115327, d160049, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d115328 q = 1) (hb : d159762 q = 1) : d160050 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d115328, d160050, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d115328, d160050, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d115332 q = 1) (hb : d159762 q = 1) : d160054 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d115332, d160054, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d115332, d160054, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31487 q ha hb
  have h12 (q : Pattern) (ha : d12590 q = 1) (hb : d159762 q = 1) : d160056 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d12590, d160056, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12590, d160056, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31466 q ha hb
  have h13 (q : Pattern) (ha : d115333 q = 1) (hb : d159762 q = 1) : d160057 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d115333, d160057, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d115333, d160057, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d115334 q = 1) (hb : d159762 q = 1) : d160058 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d115334, d160058, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d115334, d160058, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d115335 q = 1) (hb : d159762 q = 1) : d160059 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d115335, d160059, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d115335, d160059, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h16 (q : Pattern) (ha : d115336 q = 1) (hb : d159762 q = 1) : d160060 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d115336, d160060, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d115336, d160060, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d115342 q = 1) (hb : d159762 q = 1) : d160087 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d115342, d160087, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d115342, d160087, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31495 q ha hb
  have h18 (q : Pattern) (ha : d12675 q = 1) (hb : d159762 q = 1) : d160093 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d12675, d160093, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12675, d160093, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31469 q ha hb
  have h19 (q : Pattern) (ha : d115343 q = 1) (hb : d159762 q = 1) : d160094 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d115343, d160094, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d115343, d160094, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d115344 q = 1) (hb : d159762 q = 1) : d160095 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d115344, d160095, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d115344, d160095, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h21 (q : Pattern) (ha : d115345 q = 1) (hb : d159762 q = 1) : d160096 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d115345, d160096, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d115345, d160096, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h22 (q : Pattern) (ha : d115346 q = 1) (hb : d159762 q = 1) : d160097 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d115346, d160097, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d115346, d160097, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h23 (q : Pattern) (ha : d115347 q = 1) (hb : d159762 q = 1) : d160098 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d115347, d160098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d115347, d160098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
  exact h23 p ha hb
theorem andIntro31497 (p : Pattern) (ha : d115353 p = 1) (hb : d159762 p = 1) : d160104 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d159762 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d115348 q = 1) (hb : d159762 q = 1) : d160099 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d115348, d160099, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d115348, d160099, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31496 q ha hb
  have h2 (q : Pattern) (ha : d115349 q = 1) (hb : d159762 q = 1) : d160100 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d115349, d160100, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d115349, d160100, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d115350 q = 1) (hb : d159762 q = 1) : d160101 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d115350, d160101, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d115350, d160101, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d115351 q = 1) (hb : d159762 q = 1) : d160102 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d115351, d160102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d115351, d160102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d115352 q = 1) (hb : d159762 q = 1) : d160103 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d115352, d160103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d115352, d160103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d115353 q = 1) (hb : d159762 q = 1) : d160104 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d115353, d160104, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d115353, d160104, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro31498 (p : Pattern) (ha : d762 p = 1) (hb : d159762 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d754 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d100904 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d757 q = 1) (hb : d159761 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d757, d159761, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d757, d159761, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d762 q = 1) (hb : d159762 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d762, d159762, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d762, d159762, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  exact h4 p ha hb
theorem andIntro31499 (p : Pattern) (ha : d4913 p = 1) (hb : d159762 p = 1) : d160107 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d322 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d754 q = 1) (hb : d100904 q = 1) : d754 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d755 q = 1) (hb : d159761 q = 1) : d160106 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d755, d159761, d160106, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d755, d159761, d160106, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d4913 q = 1) (hb : d159762 q = 1) : d160107 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d4913, d159762, d160107, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d4913, d159762, d160107, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  exact h4 p ha hb
end NetHack.Soko22Hazard87
