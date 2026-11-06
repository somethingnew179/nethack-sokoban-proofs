import NetHack.Soko22Hazard87.AndIntroBlocks0296
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Soko22Hazard87
open NetHack.Sokoban NetHack.Sokoban.PatternCorrection
theorem andIntro74250 (p : Pattern) (ha : d288573 p = 1) (hb : d289478 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d288564 q = 1) (hb : d289469 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d288564, d289469, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro74248 q ha hb
    | true =>
      simp only [d288564, d289469, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d288565 q = 1) (hb : d289470 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d288565, d289470, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d288565, d289470, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d288570 q = 1) (hb : d289475 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d288570, d289475, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d288570, d289475, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d288571 q = 1) (hb : d289476 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d288571, d289476, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d288571, d289476, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d288572 q = 1) (hb : d289477 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d288572, d289477, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d288572, d289477, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d288573 q = 1) (hb : d289478 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d288573, d289478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d288573, d289478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro74251 (p : Pattern) (ha : d288579 p = 1) (hb : d289484 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d288574 q = 1) (hb : d289479 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d288574, d289479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro74249 q ha hb
    | true =>
      simp only [d288574, d289479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro74250 q ha hb
  have h2 (q : Pattern) (ha : d288575 q = 1) (hb : d289480 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d288575, d289480, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d288575, d289480, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d288576 q = 1) (hb : d289481 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d288576, d289481, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d288576, d289481, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d288577 q = 1) (hb : d289482 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d288577, d289482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d288577, d289482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d288578 q = 1) (hb : d289483 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d288578, d289483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d288578, d289483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d288579 q = 1) (hb : d289484 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d288579, d289484, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d288579, d289484, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro74252 (p : Pattern) (ha : d288582 p = 1) (hb : d289487 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d288560 q = 1) (hb : d289465 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d288560, d289465, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro74247 q ha hb
    | true =>
      simp only [d288560, d289465, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d288561 q = 1) (hb : d289466 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d288561, d289466, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d288561, d289466, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d288564 q = 1) (hb : d289469 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d288564, d289469, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro74248 q ha hb
    | true =>
      simp only [d288564, d289469, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d288565 q = 1) (hb : d289470 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d288565, d289470, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d288565, d289470, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d288566 q = 1) (hb : d289471 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d288566, d289471, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d288566, d289471, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d288567 q = 1) (hb : d289472 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d288567, d289472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d288567, d289472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d288568 q = 1) (hb : d289473 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d288568, d289473, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d288568, d289473, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d288582 q = 1) (hb : d289487 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d288582, d289487, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d288582, d289487, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro74253 (p : Pattern) (ha : d288583 p = 1) (hb : d289488 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d288564 q = 1) (hb : d289469 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d288564, d289469, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro74248 q ha hb
    | true =>
      simp only [d288564, d289469, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d288565 q = 1) (hb : d289470 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d288565, d289470, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d288565, d289470, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d288570 q = 1) (hb : d289475 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d288570, d289475, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d288570, d289475, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d288571 q = 1) (hb : d289476 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d288571, d289476, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d288571, d289476, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d288572 q = 1) (hb : d289477 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d288572, d289477, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d288572, d289477, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d288583 q = 1) (hb : d289488 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d288583, d289488, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d288583, d289488, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro74254 (p : Pattern) (ha : d288589 p = 1) (hb : d289494 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d288574 q = 1) (hb : d289479 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d288574, d289479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro74249 q ha hb
    | true =>
      simp only [d288574, d289479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro74250 q ha hb
  have h2 (q : Pattern) (ha : d288575 q = 1) (hb : d289480 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d288575, d289480, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d288575, d289480, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d288576 q = 1) (hb : d289481 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d288576, d289481, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d288576, d289481, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d288577 q = 1) (hb : d289482 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d288577, d289482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d288577, d289482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d288578 q = 1) (hb : d289483 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d288578, d289483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d288578, d289483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d288584 q = 1) (hb : d289489 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d288584, d289489, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro74252 q ha hb
    | true =>
      simp only [d288584, d289489, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro74253 q ha hb
  have h7 (q : Pattern) (ha : d288585 q = 1) (hb : d289490 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d288585, d289490, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d288585, d289490, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d288586 q = 1) (hb : d289491 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d288586, d289491, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d288586, d289491, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d288587 q = 1) (hb : d289492 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d288587, d289492, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d288587, d289492, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d288588 q = 1) (hb : d289493 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d288588, d289493, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d288588, d289493, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d288589 q = 1) (hb : d289494 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d288589, d289494, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d288589, d289494, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro74255 (p : Pattern) (ha : d288594 p = 1) (hb : d289499 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d288560 q = 1) (hb : d289465 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d288560, d289465, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro74247 q ha hb
    | true =>
      simp only [d288560, d289465, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d288561 q = 1) (hb : d289466 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d288561, d289466, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d288561, d289466, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d288564 q = 1) (hb : d289469 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d288564, d289469, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro74248 q ha hb
    | true =>
      simp only [d288564, d289469, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d288565 q = 1) (hb : d289470 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d288565, d289470, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d288565, d289470, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d288566 q = 1) (hb : d289471 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d288566, d289471, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d288566, d289471, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d288567 q = 1) (hb : d289472 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d288567, d289472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d288567, d289472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d288593 q = 1) (hb : d289498 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d288593, d289498, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d288593, d289498, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d288594 q = 1) (hb : d289499 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d288594, d289499, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d288594, d289499, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro74256 (p : Pattern) (ha : d288596 p = 1) (hb : d289501 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d288564 q = 1) (hb : d289469 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d288564, d289469, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro74248 q ha hb
    | true =>
      simp only [d288564, d289469, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d288565 q = 1) (hb : d289470 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d288565, d289470, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d288565, d289470, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d288570 q = 1) (hb : d289475 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d288570, d289475, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d288570, d289475, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d288571 q = 1) (hb : d289476 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d288571, d289476, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d288571, d289476, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d288595 q = 1) (hb : d289500 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d288595, d289500, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d288595, d289500, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d288596 q = 1) (hb : d289501 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d288596, d289501, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d288596, d289501, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro74257 (p : Pattern) (ha : d288603 p = 1) (hb : d289508 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d288560 q = 1) (hb : d289465 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d288560, d289465, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro74247 q ha hb
    | true =>
      simp only [d288560, d289465, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d288561 q = 1) (hb : d289466 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d288561, d289466, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d288561, d289466, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d288564 q = 1) (hb : d289469 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d288564, d289469, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro74248 q ha hb
    | true =>
      simp only [d288564, d289469, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d288565 q = 1) (hb : d289470 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d288565, d289470, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d288565, d289470, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d288566 q = 1) (hb : d289471 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d288566, d289471, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d288566, d289471, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d288601 q = 1) (hb : d289506 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d288601, d289506, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d288601, d289506, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d288602 q = 1) (hb : d289507 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d288602, d289507, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d288602, d289507, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d288603 q = 1) (hb : d289508 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d288603, d289508, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d288603, d289508, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro74258 (p : Pattern) (ha : d288606 p = 1) (hb : d289511 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d288564 q = 1) (hb : d289469 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d288564, d289469, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro74248 q ha hb
    | true =>
      simp only [d288564, d289469, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d288565 q = 1) (hb : d289470 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d288565, d289470, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d288565, d289470, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d288570 q = 1) (hb : d289475 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d288570, d289475, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d288570, d289475, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d288604 q = 1) (hb : d289509 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d288604, d289509, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d288604, d289509, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d288605 q = 1) (hb : d289510 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d288605, d289510, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d288605, d289510, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d288606 q = 1) (hb : d289511 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d288606, d289511, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d288606, d289511, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro74259 (p : Pattern) (ha : d41271 p = 1) (hb : d288616 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d30077 q = 1) (hb : d237569 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d30077, d237569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro255 q ha hb
    | true =>
      simp only [d30077, d237569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d30078 q = 1) (hb : d237570 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d30078, d237570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d30078, d237570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d40831 q = 1) (hb : d288292 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d40831, d288292, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro74209 q ha hb
    | true =>
      simp only [d40831, d288292, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d40832 q = 1) (hb : d288293 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d40832, d288293, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d40832, d288293, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d41265 q = 1) (hb : d288610 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d41265, d288610, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d41265, d288610, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d41266 q = 1) (hb : d288611 q = 1) : d0 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d41266, d288611, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d41266, d288611, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d41267 q = 1) (hb : d288612 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d41267, d288612, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d41267, d288612, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d40493 q = 1) (hb : d288033 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d40493, d288033, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro74156 q ha hb
    | true =>
      simp only [d40493, d288033, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d40494 q = 1) (hb : d288034 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d40494, d288034, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d40494, d288034, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d40833 q = 1) (hb : d288294 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d40833, d288294, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d40833, d288294, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d40837 q = 1) (hb : d288298 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d40837, d288298, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro74210 q ha hb
    | true =>
      simp only [d40837, d288298, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d40838 q = 1) (hb : d288299 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d40838, d288299, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d40838, d288299, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d41268 q = 1) (hb : d288613 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d41268, d288613, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d41268, d288613, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d41269 q = 1) (hb : d288614 q = 1) : d0 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d41269, d288614, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d41269, d288614, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d41270 q = 1) (hb : d288615 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d41270, d288615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d41270, d288615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h16 (q : Pattern) (ha : d41271 q = 1) (hb : d288616 q = 1) : d0 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d41271, d288616, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d41271, d288616, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  exact h16 p ha hb
theorem andIntro74260 (p : Pattern) (ha : d41276 p = 1) (hb : d288621 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d40831 q = 1) (hb : d288292 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d40831, d288292, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro74209 q ha hb
    | true =>
      simp only [d40831, d288292, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d40832 q = 1) (hb : d288293 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d40832, d288293, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d40832, d288293, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d40493 q = 1) (hb : d288033 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d40493, d288033, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro74156 q ha hb
    | true =>
      simp only [d40493, d288033, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d40494 q = 1) (hb : d288034 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d40494, d288034, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d40494, d288034, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d40833 q = 1) (hb : d288294 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d40833, d288294, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d40833, d288294, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d32702 q = 1) (hb : d243359 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d32702, d243359, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro61189 q ha hb
    | true =>
      simp only [d32702, d243359, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d32703 q = 1) (hb : d243360 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d32703, d243360, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d32703, d243360, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d40837 q = 1) (hb : d288298 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d40837, d288298, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro74210 q ha hb
    | true =>
      simp only [d40837, d288298, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d40838 q = 1) (hb : d288299 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d40838, d288299, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d40838, d288299, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d40839 q = 1) (hb : d288300 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d40839, d288300, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d40839, d288300, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d40840 q = 1) (hb : d288301 q = 1) : d0 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d40840, d288301, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d40840, d288301, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d40841 q = 1) (hb : d288302 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d40841, d288302, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d40841, d288302, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d40265 q = 1) (hb : d287854 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d40265, d287854, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro74117 q ha hb
    | true =>
      simp only [d40265, d287854, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d40266 q = 1) (hb : d287855 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d40266, d287855, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d40266, d287855, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d40495 q = 1) (hb : d288035 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d40495, d288035, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d40495, d288035, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d40856 q = 1) (hb : d288317 q = 1) : d0 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d40856, d288317, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d40856, d288317, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h17 (q : Pattern) (ha : d40857 q = 1) (hb : d288318 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d40857, d288318, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d40857, d288318, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h18 (q : Pattern) (ha : d41276 q = 1) (hb : d288621 q = 1) : d0 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d41276, d288621, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d41276, d288621, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro74261 (p : Pattern) (ha : d41284 p = 1) (hb : d288629 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d40831 q = 1) (hb : d288292 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d40831, d288292, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro74209 q ha hb
    | true =>
      simp only [d40831, d288292, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d40832 q = 1) (hb : d288293 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d40832, d288293, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d40832, d288293, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d40493 q = 1) (hb : d288033 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d40493, d288033, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro74156 q ha hb
    | true =>
      simp only [d40493, d288033, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d40494 q = 1) (hb : d288034 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d40494, d288034, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d40494, d288034, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d40833 q = 1) (hb : d288294 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d40833, d288294, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d40833, d288294, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d41282 q = 1) (hb : d288627 q = 1) : d0 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d41282, d288627, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d41282, d288627, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d41283 q = 1) (hb : d288628 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d41283, d288628, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d41283, d288628, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d40265 q = 1) (hb : d287854 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d40265, d287854, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro74117 q ha hb
    | true =>
      simp only [d40265, d287854, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d40266 q = 1) (hb : d287855 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d40266, d287855, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d40266, d287855, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d40495 q = 1) (hb : d288035 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d40495, d288035, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d40495, d288035, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d40856 q = 1) (hb : d288317 q = 1) : d0 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d40856, d288317, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d40856, d288317, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d40857 q = 1) (hb : d288318 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d40857, d288318, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d40857, d288318, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d41284 q = 1) (hb : d288629 q = 1) : d0 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d41284, d288629, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d41284, d288629, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  exact h13 p ha hb
theorem andIntro74262 (p : Pattern) (ha : d41290 p = 1) (hb : d288635 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d41272 q = 1) (hb : d288617 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d41272, d288617, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro74259 q ha hb
    | true =>
      simp only [d41272, d288617, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d41273 q = 1) (hb : d288618 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d41273, d288618, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d41273, d288618, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d41274 q = 1) (hb : d288619 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d41274, d288619, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d41274, d288619, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d41275 q = 1) (hb : d288620 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d41275, d288620, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d41275, d288620, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d41277 q = 1) (hb : d288622 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d41277, d288622, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro74260 q ha hb
    | true =>
      simp only [d41277, d288622, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d41278 q = 1) (hb : d288623 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d41278, d288623, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d41278, d288623, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d41279 q = 1) (hb : d288624 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d41279, d288624, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d41279, d288624, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d41280 q = 1) (hb : d288625 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d41280, d288625, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d41280, d288625, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d41281 q = 1) (hb : d288626 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d41281, d288626, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d41281, d288626, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d41285 q = 1) (hb : d288630 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d41285, d288630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro74261 q ha hb
    | true =>
      simp only [d41285, d288630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d41286 q = 1) (hb : d288631 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d41286, d288631, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d41286, d288631, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d41287 q = 1) (hb : d288632 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d41287, d288632, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d41287, d288632, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d41288 q = 1) (hb : d288633 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d41288, d288633, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d41288, d288633, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d40859 q = 1) (hb : d288320 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d40859, d288320, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro74213 q ha hb
    | true =>
      simp only [d40859, d288320, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d40860 q = 1) (hb : d288321 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d40860, d288321, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d40860, d288321, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h16 (q : Pattern) (ha : d40861 q = 1) (hb : d288322 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d40861, d288322, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d40861, d288322, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d40862 q = 1) (hb : d288323 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d40862, d288323, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d40862, d288323, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h18 (q : Pattern) (ha : d41289 q = 1) (hb : d288634 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d41289, d288634, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d41289, d288634, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d41290 q = 1) (hb : d288635 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d41290, d288635, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d41290, d288635, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro74263 (p : Pattern) (ha : d288639 p = 1) (hb : d289518 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d40859 q = 1) (hb : d288320 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d40859, d288320, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro74213 q ha hb
    | true =>
      simp only [d40859, d288320, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d40860 q = 1) (hb : d288321 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d40860, d288321, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d40860, d288321, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d40861 q = 1) (hb : d288322 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d40861, d288322, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d40861, d288322, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d40862 q = 1) (hb : d288323 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d40862, d288323, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d40862, d288323, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d288524 q = 1) (hb : d289439 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d288524, d289439, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro74241 q ha hb
    | true =>
      simp only [d288524, d289439, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d288525 q = 1) (hb : d289440 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d288525, d289440, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d288525, d289440, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d288526 q = 1) (hb : d289441 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d288526, d289441, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d288526, d289441, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d288527 q = 1) (hb : d289442 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d288527, d289442, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d288527, d289442, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d288528 q = 1) (hb : d289443 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d288528, d289443, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d288528, d289443, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d288546 q = 1) (hb : d289451 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d288546, d289451, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d288546, d289451, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h11 (q : Pattern) (ha : d288639 q = 1) (hb : d289518 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d288639, d289518, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d288639, d289518, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro74264 (p : Pattern) (ha : d288645 p = 1) (hb : d289524 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d288636 q = 1) (hb : d289515 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d288636, d289515, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro74262 q hb ha
    | true =>
      simp only [d288636, d289515, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro74242 q ha hb
  have h2 (q : Pattern) (ha : d288637 q = 1) (hb : d289516 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d288637, d289516, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d288637, d289516, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d288638 q = 1) (hb : d289517 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d288638, d289517, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d288638, d289517, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d288640 q = 1) (hb : d289519 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d288640, d289519, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro74242 q ha hb
    | true =>
      simp only [d288640, d289519, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro74263 q ha hb
  have h5 (q : Pattern) (ha : d288641 q = 1) (hb : d289520 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d288641, d289520, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d288641, d289520, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d288642 q = 1) (hb : d289521 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d288642, d289521, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d288642, d289521, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d288643 q = 1) (hb : d289522 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d288643, d289522, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d288643, d289522, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d288548 q = 1) (hb : d289453 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d288548, d289453, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro74242 q ha hb
    | true =>
      simp only [d288548, d289453, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro74245 q ha hb
  have h9 (q : Pattern) (ha : d288549 q = 1) (hb : d289454 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d288549, d289454, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d288549, d289454, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d288550 q = 1) (hb : d289455 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d288550, d289455, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d288550, d289455, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d288553 q = 1) (hb : d289458 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d288553, d289458, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro74245 q ha hb
    | true =>
      simp only [d288553, d289458, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro74246 q ha hb
  have h12 (q : Pattern) (ha : d288554 q = 1) (hb : d289459 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d288554, d289459, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d288554, d289459, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d288555 q = 1) (hb : d289460 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d288555, d289460, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d288555, d289460, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d288556 q = 1) (hb : d289461 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d288556, d289461, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d288556, d289461, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d288644 q = 1) (hb : d289523 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d288644, d289523, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d288644, d289523, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d288645 q = 1) (hb : d289524 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d288645, d289524, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d288645, d289524, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h16 p ha hb
theorem andIntro74265 (p : Pattern) (ha : d288651 p = 1) (hb : d289530 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d288646 q = 1) (hb : d289525 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d288646, d289525, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro74264 q ha hb
    | true =>
      simp only [d288646, d289525, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d288647 q = 1) (hb : d289526 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d288647, d289526, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d288647, d289526, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d288560 q = 1) (hb : d289465 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d288560, d289465, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro74247 q ha hb
    | true =>
      simp only [d288560, d289465, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d288561 q = 1) (hb : d289466 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d288561, d289466, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d288561, d289466, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d288648 q = 1) (hb : d289527 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d288648, d289527, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d288648, d289527, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d288649 q = 1) (hb : d289528 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d288649, d289528, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d288649, d289528, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d288650 q = 1) (hb : d289529 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d288650, d289529, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d288650, d289529, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d288651 q = 1) (hb : d289530 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d288651, d289530, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d288651, d289530, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro74266 (p : Pattern) (ha : d288654 p = 1) (hb : d289533 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d288541 q = 1) (hb : d289446 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d288541, d289446, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro74244 q ha hb
    | true =>
      simp only [d288541, d289446, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d288542 q = 1) (hb : d289447 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d288542, d289447, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d288542, d289447, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d288543 q = 1) (hb : d289448 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d288543, d289448, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d288543, d289448, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d288544 q = 1) (hb : d289449 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d288544, d289449, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d288544, d289449, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d288551 q = 1) (hb : d289456 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d288551, d289456, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d288551, d289456, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d288654 q = 1) (hb : d289533 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d288654, d289533, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d288654, d289533, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro74267 (p : Pattern) (ha : d288660 p = 1) (hb : d289539 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d288548 q = 1) (hb : d289453 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d288548, d289453, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro74242 q ha hb
    | true =>
      simp only [d288548, d289453, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro74245 q ha hb
  have h2 (q : Pattern) (ha : d288549 q = 1) (hb : d289454 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d288549, d289454, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d288549, d289454, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d288550 q = 1) (hb : d289455 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d288550, d289455, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d288550, d289455, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d288553 q = 1) (hb : d289458 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d288553, d289458, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro74245 q ha hb
    | true =>
      simp only [d288553, d289458, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro74246 q ha hb
  have h5 (q : Pattern) (ha : d288554 q = 1) (hb : d289459 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d288554, d289459, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d288554, d289459, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d288555 q = 1) (hb : d289460 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d288555, d289460, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d288555, d289460, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d288556 q = 1) (hb : d289461 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d288556, d289461, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d288556, d289461, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d288655 q = 1) (hb : d289534 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d288655, d289534, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro74245 q ha hb
    | true =>
      simp only [d288655, d289534, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro74266 q ha hb
  have h9 (q : Pattern) (ha : d288656 q = 1) (hb : d289535 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d288656, d289535, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d288656, d289535, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d288657 q = 1) (hb : d289536 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d288657, d289536, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d288657, d289536, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d288658 q = 1) (hb : d289537 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d288658, d289537, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d288658, d289537, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d288659 q = 1) (hb : d289538 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d288659, d289538, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d288659, d289538, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d288660 q = 1) (hb : d289539 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d288660, d289539, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d288660, d289539, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h13 p ha hb
theorem andIntro74268 (p : Pattern) (ha : d288666 p = 1) (hb : d289545 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d288661 q = 1) (hb : d289540 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d288661, d289540, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro74267 q ha hb
    | true =>
      simp only [d288661, d289540, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d288662 q = 1) (hb : d289541 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d288662, d289541, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d288662, d289541, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d288663 q = 1) (hb : d289542 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d288663, d289542, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d288663, d289542, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d288664 q = 1) (hb : d289543 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d288664, d289543, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d288664, d289543, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d288665 q = 1) (hb : d289544 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d288665, d289544, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d288665, d289544, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d288666 q = 1) (hb : d289545 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d288666, d289545, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d288666, d289545, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro74269 (p : Pattern) (ha : d288672 p = 1) (hb : d289551 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d288597 q = 1) (hb : d289502 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d288597, d289502, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro74255 q ha hb
    | true =>
      simp only [d288597, d289502, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro74256 q ha hb
  have h2 (q : Pattern) (ha : d288598 q = 1) (hb : d289503 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d288598, d289503, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d288598, d289503, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d288599 q = 1) (hb : d289504 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d288599, d289504, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d288599, d289504, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d288600 q = 1) (hb : d289505 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d288600, d289505, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d288600, d289505, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d288607 q = 1) (hb : d289512 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d288607, d289512, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro74257 q ha hb
    | true =>
      simp only [d288607, d289512, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro74258 q ha hb
  have h6 (q : Pattern) (ha : d288608 q = 1) (hb : d289513 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d288608, d289513, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d288608, d289513, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d288609 q = 1) (hb : d289514 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d288609, d289514, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d288609, d289514, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d288652 q = 1) (hb : d289531 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d288652, d289531, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro74265 q ha hb
    | true =>
      simp only [d288652, d289531, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro74249 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d288574 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d288653 q = 1) (hb : d289532 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d288653, d289532, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d288653, d289532, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
  have h11 (q : Pattern) (ha : d288667 q = 1) (hb : d289546 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d288667, d289546, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro74268 q ha hb
    | true =>
      simp only [d288667, d289546, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d288668 q = 1) (hb : d289547 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d288668, d289547, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d288668, d289547, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d288669 q = 1) (hb : d289548 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d288669, d289548, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d288669, d289548, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d288670 q = 1) (hb : d289549 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d288670, d289549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d288670, d289549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d288671 q = 1) (hb : d289550 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d288671, d289550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d288671, d289550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d288672 q = 1) (hb : d289551 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d288672, d289551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d288672, d289551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  exact h16 p ha hb
theorem andIntro74270 (p : Pattern) (ha : d288673 p = 1) (hb : d289552 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d288560 q = 1) (hb : d289465 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d288560, d289465, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro74247 q ha hb
    | true =>
      simp only [d288560, d289465, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d288561 q = 1) (hb : d289466 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d288561, d289466, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d288561, d289466, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d288564 q = 1) (hb : d289469 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d288564, d289469, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro74248 q ha hb
    | true =>
      simp only [d288564, d289469, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d288565 q = 1) (hb : d289470 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d288565, d289470, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d288565, d289470, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d288566 q = 1) (hb : d289471 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d288566, d289471, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d288566, d289471, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d288567 q = 1) (hb : d289472 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d288567, d289472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d288567, d289472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d288593 q = 1) (hb : d289498 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d288593, d289498, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d288593, d289498, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d288673 q = 1) (hb : d289552 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d288673, d289552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d288673, d289552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro74271 (p : Pattern) (ha : d288674 p = 1) (hb : d289553 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d288564 q = 1) (hb : d289469 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d288564, d289469, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro74248 q ha hb
    | true =>
      simp only [d288564, d289469, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d288565 q = 1) (hb : d289470 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d288565, d289470, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d288565, d289470, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d288570 q = 1) (hb : d289475 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d288570, d289475, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d288570, d289475, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d288571 q = 1) (hb : d289476 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d288571, d289476, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d288571, d289476, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d288595 q = 1) (hb : d289500 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d288595, d289500, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d288595, d289500, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d288674 q = 1) (hb : d289553 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d288674, d289553, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d288674, d289553, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro74272 (p : Pattern) (ha : d288679 p = 1) (hb : d289558 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d288560 q = 1) (hb : d289465 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d288560, d289465, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro74247 q ha hb
    | true =>
      simp only [d288560, d289465, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d288561 q = 1) (hb : d289466 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d288561, d289466, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d288561, d289466, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d288564 q = 1) (hb : d289469 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d288564, d289469, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro74248 q ha hb
    | true =>
      simp only [d288564, d289469, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d288565 q = 1) (hb : d289470 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d288565, d289470, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d288565, d289470, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d288566 q = 1) (hb : d289471 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d288566, d289471, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d288566, d289471, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d288601 q = 1) (hb : d289506 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d288601, d289506, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d288601, d289506, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d288602 q = 1) (hb : d289507 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d288602, d289507, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d288602, d289507, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d288679 q = 1) (hb : d289558 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d288679, d289558, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d288679, d289558, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro74273 (p : Pattern) (ha : d288680 p = 1) (hb : d289559 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d288564 q = 1) (hb : d289469 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d288564, d289469, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro74248 q ha hb
    | true =>
      simp only [d288564, d289469, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d288565 q = 1) (hb : d289470 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d288565, d289470, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d288565, d289470, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d288570 q = 1) (hb : d289475 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d288570, d289475, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d288570, d289475, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d288604 q = 1) (hb : d289509 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d288604, d289509, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d288604, d289509, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d288605 q = 1) (hb : d289510 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d288605, d289510, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d288605, d289510, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d288680 q = 1) (hb : d289559 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d288680, d289559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d288680, d289559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro74274 (p : Pattern) (ha : d288684 p = 1) (hb : d289563 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d288646 q = 1) (hb : d289525 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d288646, d289525, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro74264 q ha hb
    | true =>
      simp only [d288646, d289525, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d288647 q = 1) (hb : d289526 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d288647, d289526, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d288647, d289526, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d288560 q = 1) (hb : d289465 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d288560, d289465, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro74247 q ha hb
    | true =>
      simp only [d288560, d289465, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d288561 q = 1) (hb : d289466 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d288561, d289466, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d288561, d289466, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d288648 q = 1) (hb : d289527 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d288648, d289527, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d288648, d289527, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d288649 q = 1) (hb : d289528 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d288649, d289528, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d288649, d289528, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d288650 q = 1) (hb : d289529 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d288650, d289529, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d288650, d289529, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d288684 q = 1) (hb : d289563 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d288684, d289563, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d288684, d289563, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro74275 (p : Pattern) (ha : d288687 p = 1) (hb : d289566 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d288661 q = 1) (hb : d289540 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d288661, d289540, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro74267 q ha hb
    | true =>
      simp only [d288661, d289540, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d288662 q = 1) (hb : d289541 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d288662, d289541, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d288662, d289541, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d288663 q = 1) (hb : d289542 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d288663, d289542, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d288663, d289542, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d288664 q = 1) (hb : d289543 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d288664, d289543, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d288664, d289543, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d288665 q = 1) (hb : d289544 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d288665, d289544, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d288665, d289544, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d288687 q = 1) (hb : d289566 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d288687, d289566, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d288687, d289566, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro74276 (p : Pattern) (ha : d288693 p = 1) (hb : d289572 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d288597 q = 1) (hb : d289502 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d288597, d289502, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro74255 q ha hb
    | true =>
      simp only [d288597, d289502, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro74256 q ha hb
  have h2 (q : Pattern) (ha : d288598 q = 1) (hb : d289503 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d288598, d289503, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d288598, d289503, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d288599 q = 1) (hb : d289504 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d288599, d289504, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d288599, d289504, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d288600 q = 1) (hb : d289505 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d288600, d289505, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d288600, d289505, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d288607 q = 1) (hb : d289512 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d288607, d289512, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro74257 q ha hb
    | true =>
      simp only [d288607, d289512, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro74258 q ha hb
  have h6 (q : Pattern) (ha : d288608 q = 1) (hb : d289513 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d288608, d289513, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d288608, d289513, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d288609 q = 1) (hb : d289514 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d288609, d289514, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d288609, d289514, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d288652 q = 1) (hb : d289531 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d288652, d289531, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro74265 q ha hb
    | true =>
      simp only [d288652, d289531, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro74249 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d288574 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d288653 q = 1) (hb : d289532 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d288653, d289532, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d288653, d289532, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
  have h11 (q : Pattern) (ha : d288667 q = 1) (hb : d289546 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d288667, d289546, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro74268 q ha hb
    | true =>
      simp only [d288667, d289546, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d288668 q = 1) (hb : d289547 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d288668, d289547, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d288668, d289547, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d288669 q = 1) (hb : d289548 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d288669, d289548, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d288669, d289548, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d288670 q = 1) (hb : d289549 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d288670, d289549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d288670, d289549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d288671 q = 1) (hb : d289550 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d288671, d289550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d288671, d289550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d288675 q = 1) (hb : d289554 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d288675, d289554, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro74270 q ha hb
    | true =>
      simp only [d288675, d289554, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro74271 q ha hb
  have h17 (q : Pattern) (ha : d288676 q = 1) (hb : d289555 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d288676, d289555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d288676, d289555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d288677 q = 1) (hb : d289556 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d288677, d289556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d288677, d289556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h19 (q : Pattern) (ha : d288678 q = 1) (hb : d289557 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d288678, d289557, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d288678, d289557, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d288681 q = 1) (hb : d289560 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d288681, d289560, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro74272 q ha hb
    | true =>
      simp only [d288681, d289560, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro74273 q ha hb
  have h21 (q : Pattern) (ha : d288682 q = 1) (hb : d289561 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d288682, d289561, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d288682, d289561, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
  have h22 (q : Pattern) (ha : d288683 q = 1) (hb : d289562 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d288683, d289562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d288683, d289562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h23 (q : Pattern) (ha : d288685 q = 1) (hb : d289564 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d288685, d289564, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro74274 q ha hb
    | true =>
      simp only [d288685, d289564, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro74252 q ha hb
  have h24 (q : Pattern) (ha : d0 q = 1) (hb : d288584 q = 1) : d0 q = 1 := by
    exact ha
  have h25 (q : Pattern) (ha : d288686 q = 1) (hb : d289565 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d288686, d289565, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
    | true =>
      simp only [d288686, d289565, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q hb ha
  have h26 (q : Pattern) (ha : d288688 q = 1) (hb : d289567 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d288688, d289567, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro74275 q ha hb
    | true =>
      simp only [d288688, d289567, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h27 (q : Pattern) (ha : d288689 q = 1) (hb : d289568 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d288689, d289568, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h26 q ha hb
    | true =>
      simp only [d288689, d289568, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h28 (q : Pattern) (ha : d288690 q = 1) (hb : d289569 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d288690, d289569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q ha hb
    | true =>
      simp only [d288690, d289569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h27 q ha hb
  have h29 (q : Pattern) (ha : d288691 q = 1) (hb : d289570 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d288691, d289570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
    | true =>
      simp only [d288691, d289570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h28 q ha hb
  have h30 (q : Pattern) (ha : d288692 q = 1) (hb : d289571 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d288692, d289571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d288692, d289571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h29 q ha hb
  have h31 (q : Pattern) (ha : d288693 q = 1) (hb : d289572 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d288693, d289572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d288693, d289572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h30 q ha hb
  exact h31 p ha hb
theorem andIntro74277 (p : Pattern) (ha : d288700 p = 1) (hb : d289579 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d288574 q = 1) (hb : d289479 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d288574, d289479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro74249 q ha hb
    | true =>
      simp only [d288574, d289479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro74250 q ha hb
  have h2 (q : Pattern) (ha : d288575 q = 1) (hb : d289480 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d288575, d289480, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d288575, d289480, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d288576 q = 1) (hb : d289481 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d288576, d289481, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d288576, d289481, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d288577 q = 1) (hb : d289482 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d288577, d289482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d288577, d289482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d288578 q = 1) (hb : d289483 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d288578, d289483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d288578, d289483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d288695 q = 1) (hb : d289574 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d288695, d289574, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro74250 q ha hb
    | true =>
      simp only [d288695, d289574, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d288696 q = 1) (hb : d289575 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d288696, d289575, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d288696, d289575, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d288697 q = 1) (hb : d289576 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d288697, d289576, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d288697, d289576, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d288698 q = 1) (hb : d289577 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d288698, d289577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d288698, d289577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d288699 q = 1) (hb : d289578 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d288699, d289578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d288699, d289578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d288700 q = 1) (hb : d289579 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d288700, d289579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d288700, d289579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro74278 (p : Pattern) (ha : d288706 p = 1) (hb : d289585 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d288695 q = 1) (hb : d289574 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d288695, d289574, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro74250 q ha hb
    | true =>
      simp only [d288695, d289574, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d288696 q = 1) (hb : d289575 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d288696, d289575, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d288696, d289575, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d288697 q = 1) (hb : d289576 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d288697, d289576, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d288697, d289576, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d288698 q = 1) (hb : d289577 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d288698, d289577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d288698, d289577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d288699 q = 1) (hb : d289578 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d288699, d289578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d288699, d289578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d288701 q = 1) (hb : d289580 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d288701, d289580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro74253 q ha hb
    | true =>
      simp only [d288701, d289580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d288702 q = 1) (hb : d289581 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d288702, d289581, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d288702, d289581, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d288703 q = 1) (hb : d289582 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d288703, d289582, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d288703, d289582, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d288704 q = 1) (hb : d289583 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d288704, d289583, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d288704, d289583, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d288705 q = 1) (hb : d289584 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d288705, d289584, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d288705, d289584, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d288706 q = 1) (hb : d289585 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d288706, d289585, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d288706, d289585, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro74279 (p : Pattern) (ha : d288713 p = 1) (hb : d289592 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d288685 q = 1) (hb : d289564 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d288685, d289564, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro74274 q ha hb
    | true =>
      simp only [d288685, d289564, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro74252 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d288584 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d288686 q = 1) (hb : d289565 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d288686, d289565, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d288686, d289565, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d288688 q = 1) (hb : d289567 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d288688, d289567, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro74275 q ha hb
    | true =>
      simp only [d288688, d289567, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d288689 q = 1) (hb : d289568 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d288689, d289568, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d288689, d289568, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d288690 q = 1) (hb : d289569 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d288690, d289569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d288690, d289569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d288711 q = 1) (hb : d289590 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d288711, d289590, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d288711, d289590, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d288712 q = 1) (hb : d289591 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d288712, d289591, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d288712, d289591, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d288713 q = 1) (hb : d289592 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d288713, d289592, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d288713, d289592, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro74280 (p : Pattern) (ha : d288715 p = 1) (hb : d289594 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d288701 q = 1) (hb : d289580 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d288701, d289580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro74253 q ha hb
    | true =>
      simp only [d288701, d289580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d288702 q = 1) (hb : d289581 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d288702, d289581, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d288702, d289581, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d288703 q = 1) (hb : d289582 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d288703, d289582, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d288703, d289582, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d288704 q = 1) (hb : d289583 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d288704, d289583, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d288704, d289583, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d288705 q = 1) (hb : d289584 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d288705, d289584, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d288705, d289584, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d288715 q = 1) (hb : d289594 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d288715, d289594, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d288715, d289594, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro74281 (p : Pattern) (ha : d41487 p = 1) (hb : d288735 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d41473 q = 1) (hb : d288721 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d41473, d288721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d41473, d288721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro74259 q ha hb
  have h2 (q : Pattern) (ha : d41272 q = 1) (hb : d288617 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d41272, d288617, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro74259 q ha hb
    | true =>
      simp only [d41272, d288617, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d41474 q = 1) (hb : d288722 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d41474, d288722, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d41474, d288722, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d41273 q = 1) (hb : d288618 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d41273, d288618, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d41273, d288618, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d41475 q = 1) (hb : d288723 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d41475, d288723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d41475, d288723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d41476 q = 1) (hb : d288724 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d41476, d288724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d41476, d288724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d41477 q = 1) (hb : d288725 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d41477, d288725, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d41477, d288725, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro74260 q ha hb
  have h8 (q : Pattern) (ha : d41277 q = 1) (hb : d288622 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d41277, d288622, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro74260 q ha hb
    | true =>
      simp only [d41277, d288622, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d41478 q = 1) (hb : d288726 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d41478, d288726, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d41478, d288726, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d41278 q = 1) (hb : d288623 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d41278, d288623, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d41278, d288623, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d41479 q = 1) (hb : d288727 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d41479, d288727, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d41479, d288727, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d41480 q = 1) (hb : d288728 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d41480, d288728, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d41480, d288728, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d41481 q = 1) (hb : d288729 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d41481, d288729, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d41481, d288729, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d41482 q = 1) (hb : d288730 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d41482, d288730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d41482, d288730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro74261 q ha hb
  have h15 (q : Pattern) (ha : d41285 q = 1) (hb : d288630 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d41285, d288630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro74261 q ha hb
    | true =>
      simp only [d41285, d288630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h16 (q : Pattern) (ha : d41483 q = 1) (hb : d288731 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d41483, d288731, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d41483, d288731, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d41286 q = 1) (hb : d288631 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d41286, d288631, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d41286, d288631, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h18 (q : Pattern) (ha : d41484 q = 1) (hb : d288732 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d41484, d288732, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d41484, d288732, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d41485 q = 1) (hb : d288733 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d41485, d288733, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d41485, d288733, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h20 (q : Pattern) (ha : d41019 q = 1) (hb : d288411 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d41019, d288411, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d41019, d288411, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro74213 q ha hb
  have h21 (q : Pattern) (ha : d40859 q = 1) (hb : d288320 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d40859, d288320, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro74213 q ha hb
    | true =>
      simp only [d40859, d288320, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h22 (q : Pattern) (ha : d41020 q = 1) (hb : d288412 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d41020, d288412, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d41020, d288412, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
  have h23 (q : Pattern) (ha : d40860 q = 1) (hb : d288321 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d40860, d288321, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d40860, d288321, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h24 (q : Pattern) (ha : d41021 q = 1) (hb : d288413 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d41021, d288413, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
    | true =>
      simp only [d41021, d288413, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
  have h25 (q : Pattern) (ha : d41022 q = 1) (hb : d288414 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d41022, d288414, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q ha hb
    | true =>
      simp only [d41022, d288414, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h26 (q : Pattern) (ha : d41486 q = 1) (hb : d288734 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d41486, d288734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d41486, d288734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q ha hb
  have h27 (q : Pattern) (ha : d41487 q = 1) (hb : d288735 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d41487, d288735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d41487, d288735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h26 q ha hb
  exact h27 p ha hb
theorem andIntro74282 (p : Pattern) (ha : d288750 p = 1) (hb : d289605 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d41010 q = 1) (hb : d288736 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d41010, d288736, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d41010, d288736, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro74239 q ha hb
  have h2 (q : Pattern) (ha : d40846 q = 1) (hb : d288507 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d40846, d288507, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro74239 q ha hb
    | true =>
      simp only [d40846, d288507, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d41011 q = 1) (hb : d288737 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d41011, d288737, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d41011, d288737, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d40847 q = 1) (hb : d288508 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d40847, d288508, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d40847, d288508, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d41012 q = 1) (hb : d288738 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d41012, d288738, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d41012, d288738, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d41013 q = 1) (hb : d288739 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d41013, d288739, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d41013, d288739, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d41014 q = 1) (hb : d288740 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d41014, d288740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d41014, d288740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro74240 q ha hb
  have h8 (q : Pattern) (ha : d40851 q = 1) (hb : d288514 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d40851, d288514, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro74240 q ha hb
    | true =>
      simp only [d40851, d288514, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d41015 q = 1) (hb : d288741 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d41015, d288741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d41015, d288741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d40852 q = 1) (hb : d288515 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d40852, d288515, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d40852, d288515, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d41016 q = 1) (hb : d288742 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d41016, d288742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d41016, d288742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d41017 q = 1) (hb : d288743 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d41017, d288743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d41017, d288743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d41018 q = 1) (hb : d288744 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d41018, d288744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d41018, d288744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d41019 q = 1) (hb : d288411 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d41019, d288411, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d41019, d288411, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro74213 q ha hb
  have h15 (q : Pattern) (ha : d40859 q = 1) (hb : d288320 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d40859, d288320, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro74213 q ha hb
    | true =>
      simp only [d40859, d288320, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h16 (q : Pattern) (ha : d41020 q = 1) (hb : d288412 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d41020, d288412, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d41020, d288412, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d40860 q = 1) (hb : d288321 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d40860, d288321, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d40860, d288321, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h18 (q : Pattern) (ha : d41021 q = 1) (hb : d288413 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d41021, d288413, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d41021, d288413, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d41022 q = 1) (hb : d288414 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d41022, d288414, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d41022, d288414, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h20 (q : Pattern) (ha : d288745 q = 1) (hb : d289600 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d288745, d289600, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d288745, d289600, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro74241 q ha hb
  have h21 (q : Pattern) (ha : d288524 q = 1) (hb : d289439 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d288524, d289439, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro74241 q ha hb
    | true =>
      simp only [d288524, d289439, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h22 (q : Pattern) (ha : d288746 q = 1) (hb : d289601 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d288746, d289601, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d288746, d289601, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
  have h23 (q : Pattern) (ha : d288525 q = 1) (hb : d289440 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d288525, d289440, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d288525, d289440, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h24 (q : Pattern) (ha : d288747 q = 1) (hb : d289602 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d288747, d289602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
    | true =>
      simp only [d288747, d289602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
  have h25 (q : Pattern) (ha : d288748 q = 1) (hb : d289603 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d288748, d289603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q ha hb
    | true =>
      simp only [d288748, d289603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h26 (q : Pattern) (ha : d288749 q = 1) (hb : d289604 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d288749, d289604, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q hb ha
    | true =>
      simp only [d288749, d289604, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q ha hb
  have h27 (q : Pattern) (ha : d288750 q = 1) (hb : d289605 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d288750, d289605, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q hb ha
    | true =>
      simp only [d288750, d289605, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h26 q ha hb
  exact h27 p ha hb
theorem andIntro74283 (p : Pattern) (ha : d288755 p = 1) (hb : d289610 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d41019 q = 1) (hb : d288411 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d41019, d288411, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d41019, d288411, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro74213 q ha hb
  have h2 (q : Pattern) (ha : d40859 q = 1) (hb : d288320 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d40859, d288320, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro74213 q ha hb
    | true =>
      simp only [d40859, d288320, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d41020 q = 1) (hb : d288412 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d41020, d288412, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d41020, d288412, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d40860 q = 1) (hb : d288321 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d40860, d288321, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d40860, d288321, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d41021 q = 1) (hb : d288413 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d41021, d288413, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d41021, d288413, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d41022 q = 1) (hb : d288414 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d41022, d288414, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d41022, d288414, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d288745 q = 1) (hb : d289600 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d288745, d289600, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d288745, d289600, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro74241 q ha hb
  have h8 (q : Pattern) (ha : d288524 q = 1) (hb : d289439 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d288524, d289439, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro74241 q ha hb
    | true =>
      simp only [d288524, d289439, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d288746 q = 1) (hb : d289601 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d288746, d289601, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d288746, d289601, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d288525 q = 1) (hb : d289440 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d288525, d289440, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d288525, d289440, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h11 (q : Pattern) (ha : d288747 q = 1) (hb : d289602 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d288747, d289602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d288747, d289602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d288748 q = 1) (hb : d289603 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d288748, d289603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d288748, d289603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d288749 q = 1) (hb : d289604 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d288749, d289604, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
    | true =>
      simp only [d288749, d289604, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d288754 q = 1) (hb : d289609 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d288754, d289609, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d288754, d289609, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h15 (q : Pattern) (ha : d288755 q = 1) (hb : d289610 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d288755, d289610, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d288755, d289610, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro74284 (p : Pattern) (ha : d288769 p = 1) (hb : d289620 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d40646 q = 1) (hb : d288760 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d40646, d288760, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d40646, d288760, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro74243 q ha hb
  have h2 (q : Pattern) (ha : d40504 q = 1) (hb : d288536 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d40504, d288536, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro74243 q ha hb
    | true =>
      simp only [d40504, d288536, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d40647 q = 1) (hb : d288761 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d40647, d288761, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d40647, d288761, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d40505 q = 1) (hb : d288537 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d40505, d288537, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d40505, d288537, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d40648 q = 1) (hb : d288762 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d40648, d288762, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d40648, d288762, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d40649 q = 1) (hb : d288763 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d40649, d288763, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d40649, d288763, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d288764 q = 1) (hb : d289615 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d288764, d289615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d288764, d289615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro74244 q ha hb
  have h8 (q : Pattern) (ha : d288541 q = 1) (hb : d289446 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d288541, d289446, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro74244 q ha hb
    | true =>
      simp only [d288541, d289446, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d288765 q = 1) (hb : d289616 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d288765, d289616, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d288765, d289616, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d288542 q = 1) (hb : d289447 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d288542, d289447, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d288542, d289447, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h11 (q : Pattern) (ha : d288766 q = 1) (hb : d289617 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d288766, d289617, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d288766, d289617, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d288767 q = 1) (hb : d289618 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d288767, d289618, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d288767, d289618, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d288768 q = 1) (hb : d289619 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d288768, d289619, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
    | true =>
      simp only [d288768, d289619, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d288745 q = 1) (hb : d289600 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d288745, d289600, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d288745, d289600, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro74241 q ha hb
  have h15 (q : Pattern) (ha : d288524 q = 1) (hb : d289439 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d288524, d289439, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro74241 q ha hb
    | true =>
      simp only [d288524, d289439, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h16 (q : Pattern) (ha : d288746 q = 1) (hb : d289601 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d288746, d289601, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d288746, d289601, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d288525 q = 1) (hb : d289440 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d288525, d289440, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d288525, d289440, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h18 (q : Pattern) (ha : d288747 q = 1) (hb : d289602 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d288747, d289602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d288747, d289602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d288748 q = 1) (hb : d289603 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d288748, d289603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d288748, d289603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h20 (q : Pattern) (ha : d288754 q = 1) (hb : d289609 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d288754, d289609, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d288754, d289609, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h21 (q : Pattern) (ha : d288769 q = 1) (hb : d289620 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d288769, d289620, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d288769, d289620, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
  exact h21 p ha hb
theorem andIntro74285 (p : Pattern) (ha : d288774 p = 1) (hb : d289625 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d288764 q = 1) (hb : d289615 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d288764, d289615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d288764, d289615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro74244 q ha hb
  have h2 (q : Pattern) (ha : d288541 q = 1) (hb : d289446 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d288541, d289446, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro74244 q ha hb
    | true =>
      simp only [d288541, d289446, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d288765 q = 1) (hb : d289616 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d288765, d289616, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d288765, d289616, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d288542 q = 1) (hb : d289447 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d288542, d289447, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d288542, d289447, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d288766 q = 1) (hb : d289617 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d288766, d289617, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d288766, d289617, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d288767 q = 1) (hb : d289618 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d288767, d289618, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d288767, d289618, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d288773 q = 1) (hb : d289624 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d288773, d289624, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d288773, d289624, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d29395 q = 1) (hb : d123144 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d29395, d123144, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d29395, d123144, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro71024 q ha hb
  have h9 (q : Pattern) (ha : d29115 q = 1) (hb : d101365 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d29115, d101365, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro71024 q ha hb
    | true =>
      simp only [d29115, d101365, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d29396 q = 1) (hb : d123145 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d29396, d123145, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d29396, d123145, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d29116 q = 1) (hb : d101367 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d29116, d101367, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d29116, d101367, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d29397 q = 1) (hb : d123146 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d29397, d123146, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d29397, d123146, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d29398 q = 1) (hb : d123147 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d29398, d123147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d29398, d123147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d29399 q = 1) (hb : d123148 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d29399, d123148, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d29399, d123148, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d288774 q = 1) (hb : d289625 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d288774, d289625, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d288774, d289625, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  exact h15 p ha hb
theorem andIntro74286 (p : Pattern) (ha : d288780 p = 1) (hb : d289631 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d288751 q = 1) (hb : d289606 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d288751, d289606, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro74281 q hb ha
    | true =>
      simp only [d288751, d289606, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro74282 q ha hb
  have h2 (q : Pattern) (ha : d288752 q = 1) (hb : d289607 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d288752, d289607, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d288752, d289607, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d288753 q = 1) (hb : d289608 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d288753, d289608, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d288753, d289608, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d288756 q = 1) (hb : d289611 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d288756, d289611, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro74282 q ha hb
    | true =>
      simp only [d288756, d289611, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro74283 q ha hb
  have h5 (q : Pattern) (ha : d288757 q = 1) (hb : d289612 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d288757, d289612, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d288757, d289612, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d288758 q = 1) (hb : d289613 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d288758, d289613, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d288758, d289613, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d288759 q = 1) (hb : d289614 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d288759, d289614, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d288759, d289614, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d288770 q = 1) (hb : d289621 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d288770, d289621, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro74282 q ha hb
    | true =>
      simp only [d288770, d289621, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro74284 q ha hb
  have h9 (q : Pattern) (ha : d288771 q = 1) (hb : d289622 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d288771, d289622, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d288771, d289622, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d288772 q = 1) (hb : d289623 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d288772, d289623, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d288772, d289623, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d288775 q = 1) (hb : d289626 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d288775, d289626, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro74284 q ha hb
    | true =>
      simp only [d288775, d289626, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro74285 q ha hb
  have h12 (q : Pattern) (ha : d288776 q = 1) (hb : d289627 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d288776, d289627, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d288776, d289627, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d288777 q = 1) (hb : d289628 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d288777, d289628, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d288777, d289628, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d288778 q = 1) (hb : d289629 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d288778, d289629, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d288778, d289629, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d288779 q = 1) (hb : d289630 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d288779, d289630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d288779, d289630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d288780 q = 1) (hb : d289631 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d288780, d289631, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d288780, d289631, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h16 p ha hb
theorem andIntro74287 (p : Pattern) (ha : d288785 p = 1) (hb : d289636 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d288770 q = 1) (hb : d289621 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d288770, d289621, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro74282 q ha hb
    | true =>
      simp only [d288770, d289621, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro74284 q ha hb
  have h2 (q : Pattern) (ha : d288771 q = 1) (hb : d289622 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d288771, d289622, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d288771, d289622, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d288772 q = 1) (hb : d289623 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d288772, d289623, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d288772, d289623, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d288775 q = 1) (hb : d289626 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d288775, d289626, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro74284 q ha hb
    | true =>
      simp only [d288775, d289626, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro74285 q ha hb
  have h5 (q : Pattern) (ha : d288776 q = 1) (hb : d289627 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d288776, d289627, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d288776, d289627, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d288777 q = 1) (hb : d289628 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d288777, d289628, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d288777, d289628, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d288778 q = 1) (hb : d289629 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d288778, d289629, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d288778, d289629, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d288783 q = 1) (hb : d289634 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d288783, d289634, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d288783, d289634, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d288784 q = 1) (hb : d289635 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d288784, d289635, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d288784, d289635, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d288785 q = 1) (hb : d289636 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d288785, d289636, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d288785, d289636, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h10 p ha hb
theorem andIntro74288 (p : Pattern) (ha : d288791 p = 1) (hb : d289642 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d288781 q = 1) (hb : d289632 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d288781, d289632, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro74286 q ha hb
    | true =>
      simp only [d288781, d289632, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d288782 q = 1) (hb : d289633 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d288782, d289633, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d288782, d289633, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d288786 q = 1) (hb : d289637 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d288786, d289637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro74287 q ha hb
    | true =>
      simp only [d288786, d289637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d288787 q = 1) (hb : d289638 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d288787, d289638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d288787, d289638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d288788 q = 1) (hb : d289639 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d288788, d289639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d288788, d289639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d288789 q = 1) (hb : d289640 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d288789, d289640, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d288789, d289640, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d288790 q = 1) (hb : d289641 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d288790, d289641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d288790, d289641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d288791 q = 1) (hb : d289642 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d288791, d289642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d288791, d289642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro74289 (p : Pattern) (ha : d288793 p = 1) (hb : d289644 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d288775 q = 1) (hb : d289626 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d288775, d289626, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro74284 q ha hb
    | true =>
      simp only [d288775, d289626, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro74285 q ha hb
  have h2 (q : Pattern) (ha : d288776 q = 1) (hb : d289627 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d288776, d289627, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d288776, d289627, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d288777 q = 1) (hb : d289628 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d288777, d289628, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d288777, d289628, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d288783 q = 1) (hb : d289634 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d288783, d289634, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d288783, d289634, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d288792 q = 1) (hb : d289643 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d288792, d289643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d288792, d289643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d288793 q = 1) (hb : d289644 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d288793, d289644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d288793, d289644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro74290 (p : Pattern) (ha : d288799 p = 1) (hb : d289650 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d288786 q = 1) (hb : d289637 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d288786, d289637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro74287 q ha hb
    | true =>
      simp only [d288786, d289637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d288787 q = 1) (hb : d289638 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d288787, d289638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d288787, d289638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d288794 q = 1) (hb : d289645 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d288794, d289645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro74289 q ha hb
    | true =>
      simp only [d288794, d289645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d288795 q = 1) (hb : d289646 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d288795, d289646, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d288795, d289646, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d288796 q = 1) (hb : d289647 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d288796, d289647, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d288796, d289647, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d288797 q = 1) (hb : d289648 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d288797, d289648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d288797, d289648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d288798 q = 1) (hb : d289649 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d288798, d289649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d288798, d289649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d288799 q = 1) (hb : d289650 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d288799, d289650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d288799, d289650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro74291 (p : Pattern) (ha : d288807 p = 1) (hb : d289653 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d288764 q = 1) (hb : d289615 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d288764, d289615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d288764, d289615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro74244 q ha hb
  have h2 (q : Pattern) (ha : d288541 q = 1) (hb : d289446 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d288541, d289446, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro74244 q ha hb
    | true =>
      simp only [d288541, d289446, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d288765 q = 1) (hb : d289616 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d288765, d289616, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d288765, d289616, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d288542 q = 1) (hb : d289447 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d288542, d289447, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d288542, d289447, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d288766 q = 1) (hb : d289617 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d288766, d289617, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d288766, d289617, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d288767 q = 1) (hb : d289618 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d288767, d289618, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d288767, d289618, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d288773 q = 1) (hb : d289624 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d288773, d289624, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d288773, d289624, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d288807 q = 1) (hb : d289653 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d288807, d289653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d288807, d289653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro74292 (p : Pattern) (ha : d288813 p = 1) (hb : d289659 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d288770 q = 1) (hb : d289621 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d288770, d289621, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro74282 q ha hb
    | true =>
      simp only [d288770, d289621, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro74284 q ha hb
  have h2 (q : Pattern) (ha : d288771 q = 1) (hb : d289622 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d288771, d289622, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d288771, d289622, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d288772 q = 1) (hb : d289623 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d288772, d289623, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d288772, d289623, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d288775 q = 1) (hb : d289626 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d288775, d289626, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro74284 q ha hb
    | true =>
      simp only [d288775, d289626, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro74285 q ha hb
  have h5 (q : Pattern) (ha : d288776 q = 1) (hb : d289627 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d288776, d289627, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d288776, d289627, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d288777 q = 1) (hb : d289628 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d288777, d289628, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d288777, d289628, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d288778 q = 1) (hb : d289629 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d288778, d289629, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d288778, d289629, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d288808 q = 1) (hb : d289654 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d288808, d289654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro74284 q ha hb
    | true =>
      simp only [d288808, d289654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro74291 q ha hb
  have h9 (q : Pattern) (ha : d288809 q = 1) (hb : d289655 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d288809, d289655, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d288809, d289655, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d288810 q = 1) (hb : d289656 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d288810, d289656, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d288810, d289656, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d288811 q = 1) (hb : d289657 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d288811, d289657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d288811, d289657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d288812 q = 1) (hb : d289658 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d288812, d289658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d288812, d289658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d288813 q = 1) (hb : d289659 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d288813, d289659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d288813, d289659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h13 p ha hb
theorem andIntro74293 (p : Pattern) (ha : d288819 p = 1) (hb : d289665 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d288814 q = 1) (hb : d289660 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d288814, d289660, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro74292 q ha hb
    | true =>
      simp only [d288814, d289660, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d288815 q = 1) (hb : d289661 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d288815, d289661, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d288815, d289661, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d288816 q = 1) (hb : d289662 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d288816, d289662, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d288816, d289662, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d288817 q = 1) (hb : d289663 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d288817, d289663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d288817, d289663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d288818 q = 1) (hb : d289664 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d288818, d289664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d288818, d289664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d288819 q = 1) (hb : d289665 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d288819, d289665, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d288819, d289665, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro74294 (p : Pattern) (ha : d288825 p = 1) (hb : d289671 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d288800 q = 1) (hb : d289651 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d288800, d289651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro74288 q ha hb
    | true =>
      simp only [d288800, d289651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro74290 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d288805 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d288806 q = 1) (hb : d289652 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d288806, d289652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d288806, d289652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d288820 q = 1) (hb : d289666 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d288820, d289666, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro74293 q ha hb
    | true =>
      simp only [d288820, d289666, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d288821 q = 1) (hb : d289667 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d288821, d289667, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d288821, d289667, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d288822 q = 1) (hb : d289668 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d288822, d289668, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d288822, d289668, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d288823 q = 1) (hb : d289669 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d288823, d289669, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d288823, d289669, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d288824 q = 1) (hb : d289670 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d288824, d289670, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d288824, d289670, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d288825 q = 1) (hb : d289671 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d288825, d289671, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d288825, d289671, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro74295 (p : Pattern) (ha : d288804 p = 1) (hb : d289676 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d288794 q = 1) (hb : d289645 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d288794, d289645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro74289 q ha hb
    | true =>
      simp only [d288794, d289645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d288795 q = 1) (hb : d289646 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d288795, d289646, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d288795, d289646, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d288801 q = 1) (hb : d289673 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d288801, d289673, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d288801, d289673, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d288802 q = 1) (hb : d289674 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d288802, d289674, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d288802, d289674, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d288803 q = 1) (hb : d289675 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d288803, d289675, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d288803, d289675, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d288804 q = 1) (hb : d289676 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d288804, d289676, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d288804, d289676, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro74296 (p : Pattern) (ha : d288832 p = 1) (hb : d289682 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d288827 q = 1) (hb : d289677 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d288827, d289677, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro74295 q ha hb
    | true =>
      simp only [d288827, d289677, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d288828 q = 1) (hb : d289678 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d288828, d289678, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d288828, d289678, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d288829 q = 1) (hb : d289679 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d288829, d289679, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d288829, d289679, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d288830 q = 1) (hb : d289680 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d288830, d289680, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d288830, d289680, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d288831 q = 1) (hb : d289681 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d288831, d289681, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d288831, d289681, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d288832 q = 1) (hb : d289682 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d288832, d289682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d288832, d289682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro74297 (p : Pattern) (ha : d288838 p = 1) (hb : d289688 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d288580 q = 1) (hb : d289485 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d288580, d289485, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d288580, d289485, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro74251 q ha hb
  have h2 (q : Pattern) (ha : d288581 q = 1) (hb : d289486 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d288581, d289486, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d288581, d289486, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d288590 q = 1) (hb : d289495 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d288590, d289495, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro74251 q ha hb
    | true =>
      simp only [d288590, d289495, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro74254 q ha hb
  have h4 (q : Pattern) (ha : d288591 q = 1) (hb : d289496 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d288591, d289496, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d288591, d289496, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d288592 q = 1) (hb : d289497 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d288592, d289497, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d288592, d289497, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d288694 q = 1) (hb : d289573 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d288694, d289573, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro74269 q ha hb
    | true =>
      simp only [d288694, d289573, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro74276 q ha hb
  have h7 (q : Pattern) (ha : d288707 q = 1) (hb : d289586 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d288707, d289586, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro74277 q ha hb
    | true =>
      simp only [d288707, d289586, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro74278 q ha hb
  have h8 (q : Pattern) (ha : d288708 q = 1) (hb : d289587 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d288708, d289587, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d288708, d289587, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d288709 q = 1) (hb : d289588 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d288709, d289588, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d288709, d289588, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h10 (q : Pattern) (ha : d288710 q = 1) (hb : d289589 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d288710, d289589, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d288710, d289589, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d288714 q = 1) (hb : d289593 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d288714, d289593, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d288714, d289593, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro74279 q ha hb
  have h12 (q : Pattern) (ha : d288716 q = 1) (hb : d289595 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d288716, d289595, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d288716, d289595, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro74280 q ha hb
  have h13 (q : Pattern) (ha : d288717 q = 1) (hb : d289596 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d288717, d289596, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d288717, d289596, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d288718 q = 1) (hb : d289597 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d288718, d289597, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d288718, d289597, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h15 (q : Pattern) (ha : d288719 q = 1) (hb : d289598 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d288719, d289598, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d288719, d289598, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h16 (q : Pattern) (ha : d288720 q = 1) (hb : d289599 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d288720, d289599, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d288720, d289599, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d288826 q = 1) (hb : d289672 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d288826, d289672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d288826, d289672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro74294 q ha hb
  have h18 (q : Pattern) (ha : d288833 q = 1) (hb : d289683 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d288833, d289683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d288833, d289683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro74296 q ha hb
  have h19 (q : Pattern) (ha : d288834 q = 1) (hb : d289684 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d288834, d289684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d288834, d289684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d288835 q = 1) (hb : d289685 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d288835, d289685, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d288835, d289685, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h21 (q : Pattern) (ha : d288836 q = 1) (hb : d289686 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d288836, d289686, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d288836, d289686, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h22 (q : Pattern) (ha : d288837 q = 1) (hb : d289687 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d288837, d289687, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d288837, d289687, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h23 (q : Pattern) (ha : d288838 q = 1) (hb : d289688 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d288838, d289688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d288838, d289688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
  exact h23 p ha hb
theorem andIntro74298 (p : Pattern) (ha : d288844 p = 1) (hb : d289694 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d288839 q = 1) (hb : d289689 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d288839, d289689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d288839, d289689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro74297 q ha hb
  have h2 (q : Pattern) (ha : d288840 q = 1) (hb : d289690 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d288840, d289690, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d288840, d289690, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d288841 q = 1) (hb : d289691 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d288841, d289691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d288841, d289691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d288842 q = 1) (hb : d289692 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d288842, d289692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d288842, d289692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d288843 q = 1) (hb : d289693 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d288843, d289693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d288843, d289693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d288844 q = 1) (hb : d289694 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d288844, d289694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d288844, d289694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro74299 (p : Pattern) (ha : d41657 p = 1) (hb : d288849 p = 1) : d0 p = 1 := by
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
  have h6 (q : Pattern) (ha : d308 q = 1) (hb : d52107 q = 1) : d0 q = 1 := by
    cases bit : q 247 with
    | false =>
      simp only [d308, d52107, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d308, d52107, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d1519 q = 1) (hb : d52960 q = 1) : d0 q = 1 := by
    cases bit : q 246 with
    | false =>
      simp only [d1519, d52960, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d1519, d52960, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d40834 q = 1) (hb : d288295 q = 1) : d0 q = 1 := by
    cases bit : q 226 with
    | false =>
      simp only [d40834, d288295, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d40834, d288295, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d41656 q = 1) (hb : d288848 q = 1) : d0 q = 1 := by
    cases bit : q 225 with
    | false =>
      simp only [d41656, d288848, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d41656, d288848, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d41657 q = 1) (hb : d288849 q = 1) : d0 q = 1 := by
    cases bit : q 224 with
    | false =>
      simp only [d41657, d288849, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d41657, d288849, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro74300 (p : Pattern) (ha : d41663 p = 1) (hb : d288855 p = 1) : d0 p = 1 := by
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
  have h5 (q : Pattern) (ha : d308 q = 1) (hb : d52107 q = 1) : d0 q = 1 := by
    cases bit : q 247 with
    | false =>
      simp only [d308, d52107, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d308, d52107, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d1519 q = 1) (hb : d52960 q = 1) : d0 q = 1 := by
    cases bit : q 246 with
    | false =>
      simp only [d1519, d52960, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d1519, d52960, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d40834 q = 1) (hb : d288295 q = 1) : d0 q = 1 := by
    cases bit : q 226 with
    | false =>
      simp only [d40834, d288295, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d40834, d288295, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d41656 q = 1) (hb : d288848 q = 1) : d0 q = 1 := by
    cases bit : q 225 with
    | false =>
      simp only [d41656, d288848, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d41656, d288848, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d1531 q = 1) (hb : d52972 q = 1) : d0 q = 1 := by
    cases bit : q 226 with
    | false =>
      simp only [d1531, d52972, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d1531, d52972, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d40835 q = 1) (hb : d288296 q = 1) : d0 q = 1 := by
    cases bit : q 225 with
    | false =>
      simp only [d40835, d288296, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d40835, d288296, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d41663 q = 1) (hb : d288855 q = 1) : d0 q = 1 := by
    cases bit : q 224 with
    | false =>
      simp only [d41663, d288855, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d41663, d288855, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro74301 (p : Pattern) (ha : d41667 p = 1) (hb : d288859 p = 1) : d0 p = 1 := by
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
  have h4 (q : Pattern) (ha : d308 q = 1) (hb : d52107 q = 1) : d0 q = 1 := by
    cases bit : q 247 with
    | false =>
      simp only [d308, d52107, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d308, d52107, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d1519 q = 1) (hb : d52960 q = 1) : d0 q = 1 := by
    cases bit : q 246 with
    | false =>
      simp only [d1519, d52960, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d1519, d52960, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d40834 q = 1) (hb : d288295 q = 1) : d0 q = 1 := by
    cases bit : q 226 with
    | false =>
      simp only [d40834, d288295, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d40834, d288295, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d1531 q = 1) (hb : d52972 q = 1) : d0 q = 1 := by
    cases bit : q 226 with
    | false =>
      simp only [d1531, d52972, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d1531, d52972, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d40835 q = 1) (hb : d288296 q = 1) : d0 q = 1 := by
    cases bit : q 225 with
    | false =>
      simp only [d40835, d288296, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d40835, d288296, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d1547 q = 1) (hb : d52988 q = 1) : d0 q = 1 := by
    cases bit : q 225 with
    | false =>
      simp only [d1547, d52988, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d1547, d52988, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d41667 q = 1) (hb : d288859 q = 1) : d0 q = 1 := by
    cases bit : q 224 with
    | false =>
      simp only [d41667, d288859, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d41667, d288859, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro74302 (p : Pattern) (ha : d41695 p = 1) (hb : d288887 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d41658 q = 1) (hb : d288850 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d41658, d288850, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro74299 q ha hb
    | true =>
      simp only [d41658, d288850, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d41659 q = 1) (hb : d288851 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d41659, d288851, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d41659, d288851, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d41681 q = 1) (hb : d288873 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d41681, d288873, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro74300 q ha hb
    | true =>
      simp only [d41681, d288873, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d41682 q = 1) (hb : d288874 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d41682, d288874, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d41682, d288874, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d41692 q = 1) (hb : d288884 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d41692, d288884, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d41692, d288884, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d41693 q = 1) (hb : d288885 q = 1) : d0 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d41693, d288885, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d41693, d288885, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d41694 q = 1) (hb : d288886 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d41694, d288886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d41694, d288886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d41668 q = 1) (hb : d288860 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d41668, d288860, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro74301 q ha hb
    | true =>
      simp only [d41668, d288860, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d41669 q = 1) (hb : d288861 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d41669, d288861, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d41669, d288861, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d41683 q = 1) (hb : d288875 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d41683, d288875, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d41683, d288875, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d41684 q = 1) (hb : d288876 q = 1) : d0 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d41684, d288876, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d41684, d288876, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d41685 q = 1) (hb : d288877 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d41685, d288877, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d41685, d288877, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d41695 q = 1) (hb : d288887 q = 1) : d0 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d41695, d288887, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d41695, d288887, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  exact h13 p ha hb
theorem andIntro74303 (p : Pattern) (ha : d288865 p = 1) (hb : d289700 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d30077 q = 1) (hb : d237569 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d30077, d237569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro255 q ha hb
    | true =>
      simp only [d30077, d237569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d30078 q = 1) (hb : d237570 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d30078, d237570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d30078, d237570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d41658 q = 1) (hb : d288850 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d41658, d288850, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro74299 q ha hb
    | true =>
      simp only [d41658, d288850, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d41659 q = 1) (hb : d288851 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d41659, d288851, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d41659, d288851, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d41660 q = 1) (hb : d288852 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d41660, d288852, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d41660, d288852, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d41661 q = 1) (hb : d288853 q = 1) : d0 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d41661, d288853, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d41661, d288853, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d41662 q = 1) (hb : d288854 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d41662, d288854, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d41662, d288854, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d280256 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d41681 q = 1) (hb : d288856 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d41681, d288856, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro74300 q ha hb
    | true =>
      simp only [d41681, d288856, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d41682 q = 1) (hb : d288857 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d41682, d288857, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d41682, d288857, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d41692 q = 1) (hb : d288858 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d41692, d288858, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d41692, d288858, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d41668 q = 1) (hb : d288860 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d41668, d288860, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro74301 q ha hb
    | true =>
      simp only [d41668, d288860, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d41669 q = 1) (hb : d288861 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d41669, d288861, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d41669, d288861, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d41670 q = 1) (hb : d288862 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d41670, d288862, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d41670, d288862, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d288863 q = 1) (hb : d289698 q = 1) : d0 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d288863, d289698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
    | true =>
      simp only [d288863, d289698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d288864 q = 1) (hb : d289699 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d288864, d289699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d288864, d289699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h17 (q : Pattern) (ha : d288865 q = 1) (hb : d289700 q = 1) : d0 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d288865, d289700, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
    | true =>
      simp only [d288865, d289700, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  exact h17 p ha hb
theorem andIntro74304 (p : Pattern) (ha : d288878 p = 1) (hb : d289707 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d41658 q = 1) (hb : d288850 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d41658, d288850, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro74299 q ha hb
    | true =>
      simp only [d41658, d288850, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d41659 q = 1) (hb : d288851 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d41659, d288851, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d41659, d288851, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d280256 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d41681 q = 1) (hb : d288856 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d41681, d288856, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro74300 q ha hb
    | true =>
      simp only [d41681, d288856, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d41682 q = 1) (hb : d288857 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d41682, d288857, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d41682, d288857, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d41692 q = 1) (hb : d288858 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d41692, d288858, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d41692, d288858, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d32702 q = 1) (hb : d243359 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d32702, d243359, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro61189 q ha hb
    | true =>
      simp only [d32702, d243359, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d32703 q = 1) (hb : d243360 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d32703, d243360, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d32703, d243360, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d41668 q = 1) (hb : d288860 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d41668, d288860, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro74301 q ha hb
    | true =>
      simp only [d41668, d288860, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d41669 q = 1) (hb : d288861 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d41669, d288861, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d41669, d288861, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d41678 q = 1) (hb : d288870 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d41678, d288870, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d41678, d288870, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d288871 q = 1) (hb : d289705 q = 1) : d0 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d288871, d289705, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
    | true =>
      simp only [d288871, d289705, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
  have h13 (q : Pattern) (ha : d288872 q = 1) (hb : d289706 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d288872, d289706, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d288872, d289706, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h14 (q : Pattern) (ha : d41681 q = 1) (hb : d288873 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d41681, d288873, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro74300 q ha hb
    | true =>
      simp only [d41681, d288873, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d41682 q = 1) (hb : d288874 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d41682, d288874, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d41682, d288874, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h16 (q : Pattern) (ha : d41683 q = 1) (hb : d288875 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d41683, d288875, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d41683, d288875, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h17 (q : Pattern) (ha : d41684 q = 1) (hb : d288876 q = 1) : d0 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d41684, d288876, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d41684, d288876, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h18 (q : Pattern) (ha : d41685 q = 1) (hb : d288877 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d41685, d288877, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d41685, d288877, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h19 (q : Pattern) (ha : d288878 q = 1) (hb : d289707 q = 1) : d0 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d288878, d289707, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d288878, d289707, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q hb ha
  exact h19 p ha hb
theorem andIntro74305 (p : Pattern) (ha : d288896 p = 1) (hb : d289715 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d280256 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d41681 q = 1) (hb : d288856 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d41681, d288856, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro74300 q ha hb
    | true =>
      simp only [d41681, d288856, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d41682 q = 1) (hb : d288857 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d41682, d288857, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d41682, d288857, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d41668 q = 1) (hb : d288860 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d41668, d288860, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro74301 q ha hb
    | true =>
      simp only [d41668, d288860, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h5 (q : Pattern) (ha : d41669 q = 1) (hb : d288861 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d41669, d288861, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d41669, d288861, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h6 (q : Pattern) (ha : d41683 q = 1) (hb : d288892 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d41683, d288892, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d41683, d288892, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d41701 q = 1) (hb : d288893 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d41701, d288893, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d41701, d288893, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h8 (q : Pattern) (ha : d288894 q = 1) (hb : d289713 q = 1) : d0 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d288894, d289713, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
    | true =>
      simp only [d288894, d289713, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
  have h9 (q : Pattern) (ha : d288895 q = 1) (hb : d289714 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d288895, d289714, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d288895, d289714, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d53017 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d1564 q = 1) (hb : d53005 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d1564, d53005, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro207 q ha hb
    | true =>
      simp only [d1564, d53005, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h12 (q : Pattern) (ha : d1565 q = 1) (hb : d53006 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d1565, d53006, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d1565, d53006, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h13 (q : Pattern) (ha : d29564 q = 1) (hb : d53018 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d29564, d53018, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d29564, d53018, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d10129 q = 1) (hb : d101556 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d10129, d101556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro206 q ha hb
    | true =>
      simp only [d10129, d101556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h15 (q : Pattern) (ha : d19 q = 1) (hb : d51871 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d19, d51871, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro1 q ha hb
    | true =>
      simp only [d19, d51871, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h16 (q : Pattern) (ha : d10130 q = 1) (hb : d101557 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d10130, d101557, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d10130, d101557, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d10131 q = 1) (hb : d101558 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d10131, d101558, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d10131, d101558, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h18 (q : Pattern) (ha : d29565 q = 1) (hb : d242991 q = 1) : d0 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d29565, d242991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d29565, d242991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d29566 q = 1) (hb : d242992 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d29566, d242992, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d29566, d242992, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h20 (q : Pattern) (ha : d288896 q = 1) (hb : d289715 q = 1) : d0 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d288896, d289715, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d288896, d289715, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q hb ha
  exact h20 p ha hb
theorem andIntro74306 (p : Pattern) (ha : d288902 p = 1) (hb : d289721 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d288866 q = 1) (hb : d289701 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d288866, d289701, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro74303 q ha hb
    | true =>
      simp only [d288866, d289701, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d288867 q = 1) (hb : d289702 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d288867, d289702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d288867, d289702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d288868 q = 1) (hb : d289703 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d288868, d289703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d288868, d289703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d288869 q = 1) (hb : d289704 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d288869, d289704, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d288869, d289704, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d288879 q = 1) (hb : d289708 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d288879, d289708, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro74304 q ha hb
    | true =>
      simp only [d288879, d289708, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d288880 q = 1) (hb : d289709 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d288880, d289709, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d288880, d289709, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d288881 q = 1) (hb : d289710 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d288881, d289710, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d288881, d289710, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d288882 q = 1) (hb : d289711 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d288882, d289711, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d288882, d289711, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d288883 q = 1) (hb : d289712 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d288883, d289712, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d288883, d289712, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d41696 q = 1) (hb : d288888 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d41696, d288888, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro74302 q ha hb
    | true =>
      simp only [d41696, d288888, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d41697 q = 1) (hb : d288889 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d41697, d288889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d41697, d288889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d41698 q = 1) (hb : d288890 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d41698, d288890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d41698, d288890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d41699 q = 1) (hb : d288891 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d41699, d288891, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d41699, d288891, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d288897 q = 1) (hb : d289716 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d288897, d289716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro74305 q ha hb
    | true =>
      simp only [d288897, d289716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h15 (q : Pattern) (ha : d288898 q = 1) (hb : d289717 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d288898, d289717, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d288898, d289717, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h16 (q : Pattern) (ha : d288899 q = 1) (hb : d289718 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d288899, d289718, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d288899, d289718, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d288900 q = 1) (hb : d289719 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d288900, d289719, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d288900, d289719, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h18 (q : Pattern) (ha : d288901 q = 1) (hb : d289720 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d288901, d289720, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q hb ha
    | true =>
      simp only [d288901, d289720, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d288902 q = 1) (hb : d289721 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d288902, d289721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d288902, d289721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro74307 (p : Pattern) (ha : d288909 p = 1) (hb : d289724 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d41658 q = 1) (hb : d288850 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d41658, d288850, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro74299 q ha hb
    | true =>
      simp only [d41658, d288850, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d41659 q = 1) (hb : d288851 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d41659, d288851, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d41659, d288851, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d280256 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d41681 q = 1) (hb : d288856 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d41681, d288856, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro74300 q ha hb
    | true =>
      simp only [d41681, d288856, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d41682 q = 1) (hb : d288857 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d41682, d288857, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d41682, d288857, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d41692 q = 1) (hb : d288858 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d41692, d288858, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d41692, d288858, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d32702 q = 1) (hb : d243359 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d32702, d243359, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro61189 q ha hb
    | true =>
      simp only [d32702, d243359, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d32703 q = 1) (hb : d243360 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d32703, d243360, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d32703, d243360, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d41668 q = 1) (hb : d288860 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d41668, d288860, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro74301 q ha hb
    | true =>
      simp only [d41668, d288860, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d41669 q = 1) (hb : d288861 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d41669, d288861, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d41669, d288861, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d41678 q = 1) (hb : d288870 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d41678, d288870, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d41678, d288870, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d288871 q = 1) (hb : d289705 q = 1) : d0 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d288871, d289705, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
    | true =>
      simp only [d288871, d289705, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
  have h13 (q : Pattern) (ha : d288872 q = 1) (hb : d289706 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d288872, d289706, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d288872, d289706, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d53004 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d41668 q = 1) (hb : d288903 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d41668, d288903, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro74301 q ha hb
    | true =>
      simp only [d41668, d288903, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d41669 q = 1) (hb : d288904 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d41669, d288904, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d41669, d288904, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h17 (q : Pattern) (ha : d41683 q = 1) (hb : d288905 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d41683, d288905, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d41683, d288905, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d1564 q = 1) (hb : d53005 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d1564, d53005, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro207 q ha hb
    | true =>
      simp only [d1564, d53005, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h19 (q : Pattern) (ha : d1565 q = 1) (hb : d53006 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d1565, d53006, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d1565, d53006, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h20 (q : Pattern) (ha : d41714 q = 1) (hb : d288906 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d41714, d288906, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d41714, d288906, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
  have h21 (q : Pattern) (ha : d288907 q = 1) (hb : d289722 q = 1) : d0 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d288907, d289722, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q hb ha
    | true =>
      simp only [d288907, d289722, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q hb ha
  have h22 (q : Pattern) (ha : d288908 q = 1) (hb : d289723 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d288908, d289723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d288908, d289723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h23 (q : Pattern) (ha : d288909 q = 1) (hb : d289724 q = 1) : d0 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d288909, d289724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d288909, d289724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
  exact h23 p ha hb
theorem andIntro74308 (p : Pattern) (ha : d288914 p = 1) (hb : d289729 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d280256 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d41681 q = 1) (hb : d288856 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d41681, d288856, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro74300 q ha hb
    | true =>
      simp only [d41681, d288856, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d41682 q = 1) (hb : d288857 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d41682, d288857, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d41682, d288857, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d53004 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d41668 q = 1) (hb : d288903 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d41668, d288903, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro74301 q ha hb
    | true =>
      simp only [d41668, d288903, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d41669 q = 1) (hb : d288904 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d41669, d288904, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d41669, d288904, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h7 (q : Pattern) (ha : d41683 q = 1) (hb : d288905 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d41683, d288905, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d41683, d288905, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d41668 q = 1) (hb : d288860 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d41668, d288860, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro74301 q ha hb
    | true =>
      simp only [d41668, d288860, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h9 (q : Pattern) (ha : d41669 q = 1) (hb : d288861 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d41669, d288861, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d41669, d288861, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h10 (q : Pattern) (ha : d1564 q = 1) (hb : d53005 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d1564, d53005, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro207 q ha hb
    | true =>
      simp only [d1564, d53005, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h11 (q : Pattern) (ha : d1565 q = 1) (hb : d53006 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d1565, d53006, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d1565, d53006, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h12 (q : Pattern) (ha : d41714 q = 1) (hb : d288906 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d41714, d288906, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d41714, d288906, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d288907 q = 1) (hb : d289722 q = 1) : d0 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d288907, d289722, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
    | true =>
      simp only [d288907, d289722, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
  have h14 (q : Pattern) (ha : d288908 q = 1) (hb : d289723 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d288908, d289723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d288908, d289723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h15 (q : Pattern) (ha : d0 q = 1) (hb : d53017 q = 1) : d0 q = 1 := by
    exact ha
  have h16 (q : Pattern) (ha : d29564 q = 1) (hb : d53018 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d29564, d53018, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d29564, d53018, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h17 (q : Pattern) (ha : d10129 q = 1) (hb : d101556 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d10129, d101556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro206 q ha hb
    | true =>
      simp only [d10129, d101556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h18 (q : Pattern) (ha : d19 q = 1) (hb : d51871 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d19, d51871, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro1 q ha hb
    | true =>
      simp only [d19, d51871, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h19 (q : Pattern) (ha : d10130 q = 1) (hb : d101557 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d10130, d101557, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d10130, d101557, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d10131 q = 1) (hb : d101558 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d10131, d101558, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d10131, d101558, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h21 (q : Pattern) (ha : d29565 q = 1) (hb : d242991 q = 1) : d0 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d29565, d242991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d29565, d242991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
  have h22 (q : Pattern) (ha : d29566 q = 1) (hb : d242992 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d29566, d242992, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d29566, d242992, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h23 (q : Pattern) (ha : d288914 q = 1) (hb : d289729 q = 1) : d0 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d288914, d289729, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d288914, d289729, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q hb ha
  exact h23 p ha hb
theorem andIntro74309 (p : Pattern) (ha : d288921 p = 1) (hb : d289736 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d288910 q = 1) (hb : d289725 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d288910, d289725, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro74307 q ha hb
    | true =>
      simp only [d288910, d289725, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d288911 q = 1) (hb : d289726 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d288911, d289726, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d288911, d289726, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d288912 q = 1) (hb : d289727 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d288912, d289727, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d288912, d289727, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d288913 q = 1) (hb : d289728 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d288913, d289728, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d288913, d289728, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d288915 q = 1) (hb : d289730 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d288915, d289730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro74308 q ha hb
    | true =>
      simp only [d288915, d289730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d288916 q = 1) (hb : d289731 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d288916, d289731, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d288916, d289731, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d288917 q = 1) (hb : d289732 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d288917, d289732, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d288917, d289732, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d288918 q = 1) (hb : d289733 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d288918, d289733, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d288918, d289733, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d288919 q = 1) (hb : d289734 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d288919, d289734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d288919, d289734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d288897 q = 1) (hb : d289716 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d288897, d289716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro74305 q ha hb
    | true =>
      simp only [d288897, d289716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h11 (q : Pattern) (ha : d288898 q = 1) (hb : d289717 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d288898, d289717, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d288898, d289717, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d288899 q = 1) (hb : d289718 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d288899, d289718, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d288899, d289718, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d288900 q = 1) (hb : d289719 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d288900, d289719, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d288900, d289719, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h14 (q : Pattern) (ha : d288920 q = 1) (hb : d289735 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d288920, d289735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d288920, d289735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h15 (q : Pattern) (ha : d288921 q = 1) (hb : d289736 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d288921, d289736, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d288921, d289736, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro74310 (p : Pattern) (ha : d288926 p = 1) (hb : d289741 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d288915 q = 1) (hb : d289730 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d288915, d289730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro74308 q ha hb
    | true =>
      simp only [d288915, d289730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d288916 q = 1) (hb : d289731 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d288916, d289731, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d288916, d289731, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d288917 q = 1) (hb : d289732 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d288917, d289732, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d288917, d289732, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d288918 q = 1) (hb : d289733 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d288918, d289733, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d288918, d289733, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d288925 q = 1) (hb : d289740 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d288925, d289740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d288925, d289740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d29596 q = 1) (hb : d101562 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d29596, d101562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro71084 q ha hb
    | true =>
      simp only [d29596, d101562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d29597 q = 1) (hb : d101564 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d29597, d101564, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d29597, d101564, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d29598 q = 1) (hb : d123248 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d29598, d123248, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d29598, d123248, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d29599 q = 1) (hb : d123249 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d29599, d123249, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d29599, d123249, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d29600 q = 1) (hb : d123250 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d29600, d123250, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d29600, d123250, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d288926 q = 1) (hb : d289741 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d288926, d289741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d288926, d289741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
  exact h11 p ha hb
theorem andIntro74311 (p : Pattern) (ha : d288933 p = 1) (hb : d289748 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d288922 q = 1) (hb : d289737 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d288922, d289737, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro74306 q ha hb
    | true =>
      simp only [d288922, d289737, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro74309 q ha hb
  have h2 (q : Pattern) (ha : d288923 q = 1) (hb : d289738 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d288923, d289738, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d288923, d289738, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d288924 q = 1) (hb : d289739 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d288924, d289739, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d288924, d289739, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d288927 q = 1) (hb : d289742 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d288927, d289742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro74309 q ha hb
    | true =>
      simp only [d288927, d289742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro74310 q ha hb
  have h5 (q : Pattern) (ha : d288928 q = 1) (hb : d289743 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d288928, d289743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d288928, d289743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d288929 q = 1) (hb : d289744 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d288929, d289744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d288929, d289744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d288930 q = 1) (hb : d289745 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d288930, d289745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d288930, d289745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d288931 q = 1) (hb : d289746 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d288931, d289746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d288931, d289746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d288932 q = 1) (hb : d289747 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d288932, d289747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d288932, d289747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d288933 q = 1) (hb : d289748 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d288933, d289748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d288933, d289748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h10 p ha hb
theorem andIntro74312 (p : Pattern) (ha : d288937 p = 1) (hb : d289752 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d288927 q = 1) (hb : d289742 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d288927, d289742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro74309 q ha hb
    | true =>
      simp only [d288927, d289742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro74310 q ha hb
  have h2 (q : Pattern) (ha : d288928 q = 1) (hb : d289743 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d288928, d289743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d288928, d289743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d288929 q = 1) (hb : d289744 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d288929, d289744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d288929, d289744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d288931 q = 1) (hb : d289746 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d288931, d289746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d288931, d289746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d288936 q = 1) (hb : d289751 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d288936, d289751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d288936, d289751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d288937 q = 1) (hb : d289752 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d288937, d289752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d288937, d289752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro74313 (p : Pattern) (ha : d288943 p = 1) (hb : d289758 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d288934 q = 1) (hb : d289749 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d288934, d289749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro74311 q ha hb
    | true =>
      simp only [d288934, d289749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d288935 q = 1) (hb : d289750 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d288935, d289750, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d288935, d289750, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d288938 q = 1) (hb : d289753 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d288938, d289753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro74312 q ha hb
    | true =>
      simp only [d288938, d289753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d288939 q = 1) (hb : d289754 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d288939, d289754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d288939, d289754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d288940 q = 1) (hb : d289755 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d288940, d289755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d288940, d289755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d288941 q = 1) (hb : d289756 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d288941, d289756, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d288941, d289756, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d288942 q = 1) (hb : d289757 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d288942, d289757, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d288942, d289757, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d288943 q = 1) (hb : d289758 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d288943, d289758, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d288943, d289758, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro74314 (p : Pattern) (ha : d288947 p = 1) (hb : d289762 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d288938 q = 1) (hb : d289753 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d288938, d289753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro74312 q ha hb
    | true =>
      simp only [d288938, d289753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d288939 q = 1) (hb : d289754 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d288939, d289754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d288939, d289754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d288944 q = 1) (hb : d289759 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d288944, d289759, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d288944, d289759, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d288945 q = 1) (hb : d289760 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d288945, d289760, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d288945, d289760, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d288946 q = 1) (hb : d289761 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d288946, d289761, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d288946, d289761, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d288947 q = 1) (hb : d289762 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d288947, d289762, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d288947, d289762, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro74315 (p : Pattern) (ha : d288953 p = 1) (hb : d289768 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d288948 q = 1) (hb : d289763 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d288948, d289763, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro74313 q ha hb
    | true =>
      simp only [d288948, d289763, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro74314 q ha hb
  have h2 (q : Pattern) (ha : d288949 q = 1) (hb : d289764 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d288949, d289764, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d288949, d289764, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d288950 q = 1) (hb : d289765 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d288950, d289765, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d288950, d289765, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d288951 q = 1) (hb : d289766 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d288951, d289766, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d288951, d289766, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d288952 q = 1) (hb : d289767 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d288952, d289767, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d288952, d289767, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d288953 q = 1) (hb : d289768 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d288953, d289768, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d288953, d289768, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro74316 (p : Pattern) (ha : d288956 p = 1) (hb : d289771 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d288934 q = 1) (hb : d289749 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d288934, d289749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro74311 q ha hb
    | true =>
      simp only [d288934, d289749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d288935 q = 1) (hb : d289750 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d288935, d289750, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d288935, d289750, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d288938 q = 1) (hb : d289753 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d288938, d289753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro74312 q ha hb
    | true =>
      simp only [d288938, d289753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d288939 q = 1) (hb : d289754 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d288939, d289754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d288939, d289754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d288940 q = 1) (hb : d289755 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d288940, d289755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d288940, d289755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d288941 q = 1) (hb : d289756 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d288941, d289756, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d288941, d289756, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d288942 q = 1) (hb : d289757 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d288942, d289757, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d288942, d289757, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d288956 q = 1) (hb : d289771 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d288956, d289771, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d288956, d289771, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro74317 (p : Pattern) (ha : d288957 p = 1) (hb : d289772 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d288938 q = 1) (hb : d289753 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d288938, d289753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro74312 q ha hb
    | true =>
      simp only [d288938, d289753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d288939 q = 1) (hb : d289754 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d288939, d289754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d288939, d289754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d288944 q = 1) (hb : d289759 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d288944, d289759, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d288944, d289759, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d288945 q = 1) (hb : d289760 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d288945, d289760, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d288945, d289760, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d288946 q = 1) (hb : d289761 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d288946, d289761, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d288946, d289761, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d288957 q = 1) (hb : d289772 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d288957, d289772, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d288957, d289772, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro74318 (p : Pattern) (ha : d288963 p = 1) (hb : d289778 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d288948 q = 1) (hb : d289763 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d288948, d289763, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro74313 q ha hb
    | true =>
      simp only [d288948, d289763, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro74314 q ha hb
  have h2 (q : Pattern) (ha : d288949 q = 1) (hb : d289764 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d288949, d289764, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d288949, d289764, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d288950 q = 1) (hb : d289765 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d288950, d289765, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d288950, d289765, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d288951 q = 1) (hb : d289766 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d288951, d289766, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d288951, d289766, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d288952 q = 1) (hb : d289767 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d288952, d289767, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d288952, d289767, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d288958 q = 1) (hb : d289773 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d288958, d289773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro74316 q ha hb
    | true =>
      simp only [d288958, d289773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro74317 q ha hb
  have h7 (q : Pattern) (ha : d288959 q = 1) (hb : d289774 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d288959, d289774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d288959, d289774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d288960 q = 1) (hb : d289775 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d288960, d289775, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d288960, d289775, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d288961 q = 1) (hb : d289776 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d288961, d289776, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d288961, d289776, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d288962 q = 1) (hb : d289777 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d288962, d289777, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d288962, d289777, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d288963 q = 1) (hb : d289778 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d288963, d289778, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d288963, d289778, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro74319 (p : Pattern) (ha : d288968 p = 1) (hb : d289783 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d288934 q = 1) (hb : d289749 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d288934, d289749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro74311 q ha hb
    | true =>
      simp only [d288934, d289749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d288935 q = 1) (hb : d289750 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d288935, d289750, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d288935, d289750, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d288938 q = 1) (hb : d289753 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d288938, d289753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro74312 q ha hb
    | true =>
      simp only [d288938, d289753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d288939 q = 1) (hb : d289754 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d288939, d289754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d288939, d289754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d288940 q = 1) (hb : d289755 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d288940, d289755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d288940, d289755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d288941 q = 1) (hb : d289756 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d288941, d289756, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d288941, d289756, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d288967 q = 1) (hb : d289782 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d288967, d289782, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d288967, d289782, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d288968 q = 1) (hb : d289783 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d288968, d289783, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d288968, d289783, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro74320 (p : Pattern) (ha : d288970 p = 1) (hb : d289785 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d288938 q = 1) (hb : d289753 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d288938, d289753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro74312 q ha hb
    | true =>
      simp only [d288938, d289753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d288939 q = 1) (hb : d289754 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d288939, d289754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d288939, d289754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d288944 q = 1) (hb : d289759 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d288944, d289759, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d288944, d289759, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d288945 q = 1) (hb : d289760 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d288945, d289760, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d288945, d289760, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d288969 q = 1) (hb : d289784 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d288969, d289784, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d288969, d289784, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d288970 q = 1) (hb : d289785 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d288970, d289785, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d288970, d289785, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro74321 (p : Pattern) (ha : d288977 p = 1) (hb : d289792 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d288934 q = 1) (hb : d289749 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d288934, d289749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro74311 q ha hb
    | true =>
      simp only [d288934, d289749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d288935 q = 1) (hb : d289750 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d288935, d289750, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d288935, d289750, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d288938 q = 1) (hb : d289753 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d288938, d289753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro74312 q ha hb
    | true =>
      simp only [d288938, d289753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d288939 q = 1) (hb : d289754 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d288939, d289754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d288939, d289754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d288940 q = 1) (hb : d289755 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d288940, d289755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d288940, d289755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d288975 q = 1) (hb : d289790 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d288975, d289790, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d288975, d289790, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d288976 q = 1) (hb : d289791 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d288976, d289791, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d288976, d289791, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d288977 q = 1) (hb : d289792 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d288977, d289792, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d288977, d289792, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro74322 (p : Pattern) (ha : d288980 p = 1) (hb : d289795 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d288938 q = 1) (hb : d289753 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d288938, d289753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro74312 q ha hb
    | true =>
      simp only [d288938, d289753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d288939 q = 1) (hb : d289754 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d288939, d289754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d288939, d289754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d288944 q = 1) (hb : d289759 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d288944, d289759, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d288944, d289759, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d288978 q = 1) (hb : d289793 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d288978, d289793, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d288978, d289793, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d288979 q = 1) (hb : d289794 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d288979, d289794, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d288979, d289794, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d288980 q = 1) (hb : d289795 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d288980, d289795, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d288980, d289795, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro74323 (p : Pattern) (ha : d41792 p = 1) (hb : d288984 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d30077 q = 1) (hb : d237569 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d30077, d237569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro255 q ha hb
    | true =>
      simp only [d30077, d237569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d30078 q = 1) (hb : d237570 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d30078, d237570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d30078, d237570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d30079 q = 1) (hb : d237571 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d30079, d237571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d30079, d237571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d30080 q = 1) (hb : d237572 q = 1) : d0 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d30080, d237572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d30080, d237572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d30081 q = 1) (hb : d237573 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d30081, d237573, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d30081, d237573, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d41658 q = 1) (hb : d288850 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d41658, d288850, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro74299 q ha hb
    | true =>
      simp only [d41658, d288850, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d41659 q = 1) (hb : d288851 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d41659, d288851, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d41659, d288851, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d41660 q = 1) (hb : d288852 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d41660, d288852, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d41660, d288852, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d41661 q = 1) (hb : d288853 q = 1) : d0 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d41661, d288853, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d41661, d288853, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d41662 q = 1) (hb : d288854 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d41662, d288854, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d41662, d288854, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d41792 q = 1) (hb : d288984 q = 1) : d0 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d41792, d288984, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d41792, d288984, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro74324 (p : Pattern) (ha : d41797 p = 1) (hb : d288989 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d30077 q = 1) (hb : d237569 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d30077, d237569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro255 q ha hb
    | true =>
      simp only [d30077, d237569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d30078 q = 1) (hb : d237570 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d30078, d237570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d30078, d237570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d41658 q = 1) (hb : d288850 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d41658, d288850, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro74299 q ha hb
    | true =>
      simp only [d41658, d288850, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d41659 q = 1) (hb : d288851 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d41659, d288851, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d41659, d288851, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d41660 q = 1) (hb : d288852 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d41660, d288852, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d41660, d288852, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d41661 q = 1) (hb : d288853 q = 1) : d0 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d41661, d288853, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d41661, d288853, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d41662 q = 1) (hb : d288854 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d41662, d288854, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d41662, d288854, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d41681 q = 1) (hb : d288873 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d41681, d288873, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro74300 q ha hb
    | true =>
      simp only [d41681, d288873, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d41682 q = 1) (hb : d288874 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d41682, d288874, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d41682, d288874, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d41692 q = 1) (hb : d288884 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d41692, d288884, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d41692, d288884, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d41693 q = 1) (hb : d288885 q = 1) : d0 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d41693, d288885, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d41693, d288885, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d41694 q = 1) (hb : d288886 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d41694, d288886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d41694, d288886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d41797 q = 1) (hb : d288989 q = 1) : d0 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d41797, d288989, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d41797, d288989, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  exact h13 p ha hb
theorem andIntro74325 (p : Pattern) (ha : d41804 p = 1) (hb : d288996 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d41793 q = 1) (hb : d288985 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d41793, d288985, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro74323 q ha hb
    | true =>
      simp only [d41793, d288985, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d41794 q = 1) (hb : d288986 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d41794, d288986, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d41794, d288986, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d41795 q = 1) (hb : d288987 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d41795, d288987, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d41795, d288987, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d41796 q = 1) (hb : d288988 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d41796, d288988, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d41796, d288988, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d41798 q = 1) (hb : d288990 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d41798, d288990, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro74324 q ha hb
    | true =>
      simp only [d41798, d288990, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d41799 q = 1) (hb : d288991 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d41799, d288991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d41799, d288991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d41800 q = 1) (hb : d288992 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d41800, d288992, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d41800, d288992, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d41801 q = 1) (hb : d288993 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d41801, d288993, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d41801, d288993, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d41802 q = 1) (hb : d288994 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d41802, d288994, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d41802, d288994, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d41696 q = 1) (hb : d288888 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d41696, d288888, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro74302 q ha hb
    | true =>
      simp only [d41696, d288888, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d41697 q = 1) (hb : d288889 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d41697, d288889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d41697, d288889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d41698 q = 1) (hb : d288890 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d41698, d288890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d41698, d288890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d41699 q = 1) (hb : d288891 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d41699, d288891, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d41699, d288891, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d41803 q = 1) (hb : d288995 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d41803, d288995, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d41803, d288995, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d41804 q = 1) (hb : d288996 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d41804, d288996, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d41804, d288996, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro74326 (p : Pattern) (ha : d289000 p = 1) (hb : d289802 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d41696 q = 1) (hb : d288888 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d41696, d288888, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro74302 q ha hb
    | true =>
      simp only [d41696, d288888, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d41697 q = 1) (hb : d288889 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d41697, d288889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d41697, d288889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d41698 q = 1) (hb : d288890 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d41698, d288890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d41698, d288890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d41699 q = 1) (hb : d288891 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d41699, d288891, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d41699, d288891, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d288897 q = 1) (hb : d289716 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d288897, d289716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro74305 q ha hb
    | true =>
      simp only [d288897, d289716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d288898 q = 1) (hb : d289717 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d288898, d289717, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d288898, d289717, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d288899 q = 1) (hb : d289718 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d288899, d289718, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d288899, d289718, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d288900 q = 1) (hb : d289719 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d288900, d289719, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d288900, d289719, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d288901 q = 1) (hb : d289720 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d288901, d289720, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d288901, d289720, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d288920 q = 1) (hb : d289735 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d288920, d289735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d288920, d289735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h11 (q : Pattern) (ha : d289000 q = 1) (hb : d289802 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d289000, d289802, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d289000, d289802, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro74327 (p : Pattern) (ha : d289006 p = 1) (hb : d289808 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d288997 q = 1) (hb : d289799 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d288997, d289799, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro74325 q hb ha
    | true =>
      simp only [d288997, d289799, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro74306 q ha hb
  have h2 (q : Pattern) (ha : d288998 q = 1) (hb : d289800 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d288998, d289800, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d288998, d289800, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d288999 q = 1) (hb : d289801 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d288999, d289801, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d288999, d289801, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d289001 q = 1) (hb : d289803 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d289001, d289803, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro74306 q ha hb
    | true =>
      simp only [d289001, d289803, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro74326 q ha hb
  have h5 (q : Pattern) (ha : d289002 q = 1) (hb : d289804 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d289002, d289804, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d289002, d289804, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d289003 q = 1) (hb : d289805 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d289003, d289805, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d289003, d289805, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d289004 q = 1) (hb : d289806 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d289004, d289806, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d289004, d289806, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d288922 q = 1) (hb : d289737 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d288922, d289737, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro74306 q ha hb
    | true =>
      simp only [d288922, d289737, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro74309 q ha hb
  have h9 (q : Pattern) (ha : d288923 q = 1) (hb : d289738 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d288923, d289738, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d288923, d289738, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d288924 q = 1) (hb : d289739 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d288924, d289739, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d288924, d289739, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d288927 q = 1) (hb : d289742 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d288927, d289742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro74309 q ha hb
    | true =>
      simp only [d288927, d289742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro74310 q ha hb
  have h12 (q : Pattern) (ha : d288928 q = 1) (hb : d289743 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d288928, d289743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d288928, d289743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d288929 q = 1) (hb : d289744 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d288929, d289744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d288929, d289744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d288930 q = 1) (hb : d289745 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d288930, d289745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d288930, d289745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d289005 q = 1) (hb : d289807 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d289005, d289807, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d289005, d289807, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d289006 q = 1) (hb : d289808 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d289006, d289808, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d289006, d289808, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h16 p ha hb
theorem andIntro74328 (p : Pattern) (ha : d289012 p = 1) (hb : d289814 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d289007 q = 1) (hb : d289809 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d289007, d289809, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro74327 q ha hb
    | true =>
      simp only [d289007, d289809, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d289008 q = 1) (hb : d289810 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d289008, d289810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d289008, d289810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d288934 q = 1) (hb : d289749 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d288934, d289749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro74311 q ha hb
    | true =>
      simp only [d288934, d289749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d288935 q = 1) (hb : d289750 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d288935, d289750, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d288935, d289750, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d289009 q = 1) (hb : d289811 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d289009, d289811, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d289009, d289811, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d289010 q = 1) (hb : d289812 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d289010, d289812, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d289010, d289812, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d289011 q = 1) (hb : d289813 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d289011, d289813, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d289011, d289813, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d289012 q = 1) (hb : d289814 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d289012, d289814, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d289012, d289814, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro74329 (p : Pattern) (ha : d289015 p = 1) (hb : d289817 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d280256 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d41681 q = 1) (hb : d288856 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d41681, d288856, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro74300 q ha hb
    | true =>
      simp only [d41681, d288856, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d41682 q = 1) (hb : d288857 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d41682, d288857, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d41682, d288857, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d41668 q = 1) (hb : d288860 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d41668, d288860, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro74301 q ha hb
    | true =>
      simp only [d41668, d288860, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h5 (q : Pattern) (ha : d41669 q = 1) (hb : d288861 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d41669, d288861, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d41669, d288861, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h6 (q : Pattern) (ha : d41683 q = 1) (hb : d288892 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d41683, d288892, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d41683, d288892, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d41701 q = 1) (hb : d288893 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d41701, d288893, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d41701, d288893, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h8 (q : Pattern) (ha : d288894 q = 1) (hb : d289713 q = 1) : d0 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d288894, d289713, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
    | true =>
      simp only [d288894, d289713, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
  have h9 (q : Pattern) (ha : d288895 q = 1) (hb : d289714 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d288895, d289714, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d288895, d289714, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d69216 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d1564 q = 1) (hb : d53005 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d1564, d53005, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro207 q ha hb
    | true =>
      simp only [d1564, d53005, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h12 (q : Pattern) (ha : d1565 q = 1) (hb : d53006 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d1565, d53006, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d1565, d53006, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h13 (q : Pattern) (ha : d29564 q = 1) (hb : d69217 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d29564, d69217, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d29564, d69217, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d1578 q = 1) (hb : d53019 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d1578, d53019, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d1578, d53019, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h15 (q : Pattern) (ha : d29787 q = 1) (hb : d69218 q = 1) : d0 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d29787, d69218, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d29787, d69218, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d29788 q = 1) (hb : d69219 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d29788, d69219, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d29788, d69219, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h17 (q : Pattern) (ha : d289015 q = 1) (hb : d289817 q = 1) : d0 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d289015, d289817, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d289015, d289817, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q hb ha
  exact h17 p ha hb
theorem andIntro74330 (p : Pattern) (ha : d289021 p = 1) (hb : d289823 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d288910 q = 1) (hb : d289725 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d288910, d289725, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro74307 q ha hb
    | true =>
      simp only [d288910, d289725, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d288911 q = 1) (hb : d289726 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d288911, d289726, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d288911, d289726, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d288912 q = 1) (hb : d289727 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d288912, d289727, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d288912, d289727, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d288913 q = 1) (hb : d289728 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d288913, d289728, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d288913, d289728, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d288915 q = 1) (hb : d289730 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d288915, d289730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro74308 q ha hb
    | true =>
      simp only [d288915, d289730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d288916 q = 1) (hb : d289731 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d288916, d289731, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d288916, d289731, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d288917 q = 1) (hb : d289732 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d288917, d289732, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d288917, d289732, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d288918 q = 1) (hb : d289733 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d288918, d289733, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d288918, d289733, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d288919 q = 1) (hb : d289734 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d288919, d289734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d288919, d289734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d289016 q = 1) (hb : d289818 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d289016, d289818, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro74329 q ha hb
    | true =>
      simp only [d289016, d289818, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h11 (q : Pattern) (ha : d289017 q = 1) (hb : d289819 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d289017, d289819, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d289017, d289819, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d289018 q = 1) (hb : d289820 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d289018, d289820, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d289018, d289820, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d289019 q = 1) (hb : d289821 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d289019, d289821, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d289019, d289821, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h14 (q : Pattern) (ha : d289020 q = 1) (hb : d289822 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d289020, d289822, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d289020, d289822, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h15 (q : Pattern) (ha : d289021 q = 1) (hb : d289823 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d289021, d289823, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d289021, d289823, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro74331 (p : Pattern) (ha : d289022 p = 1) (hb : d289824 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d280256 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d41681 q = 1) (hb : d288856 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d41681, d288856, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro74300 q ha hb
    | true =>
      simp only [d41681, d288856, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d41682 q = 1) (hb : d288857 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d41682, d288857, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d41682, d288857, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d53004 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d41668 q = 1) (hb : d288903 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d41668, d288903, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro74301 q ha hb
    | true =>
      simp only [d41668, d288903, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d41669 q = 1) (hb : d288904 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d41669, d288904, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d41669, d288904, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h7 (q : Pattern) (ha : d41683 q = 1) (hb : d288905 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d41683, d288905, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d41683, d288905, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d41668 q = 1) (hb : d288860 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d41668, d288860, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro74301 q ha hb
    | true =>
      simp only [d41668, d288860, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h9 (q : Pattern) (ha : d41669 q = 1) (hb : d288861 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d41669, d288861, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d41669, d288861, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h10 (q : Pattern) (ha : d1564 q = 1) (hb : d53005 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d1564, d53005, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro207 q ha hb
    | true =>
      simp only [d1564, d53005, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h11 (q : Pattern) (ha : d1565 q = 1) (hb : d53006 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d1565, d53006, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d1565, d53006, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h12 (q : Pattern) (ha : d41714 q = 1) (hb : d288906 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d41714, d288906, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d41714, d288906, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d288907 q = 1) (hb : d289722 q = 1) : d0 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d288907, d289722, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
    | true =>
      simp only [d288907, d289722, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
  have h14 (q : Pattern) (ha : d288908 q = 1) (hb : d289723 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d288908, d289723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d288908, d289723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h15 (q : Pattern) (ha : d0 q = 1) (hb : d69216 q = 1) : d0 q = 1 := by
    exact ha
  have h16 (q : Pattern) (ha : d29564 q = 1) (hb : d69217 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d29564, d69217, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d29564, d69217, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h17 (q : Pattern) (ha : d1578 q = 1) (hb : d53019 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d1578, d53019, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d1578, d53019, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h18 (q : Pattern) (ha : d29787 q = 1) (hb : d69218 q = 1) : d0 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d29787, d69218, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d29787, d69218, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d29788 q = 1) (hb : d69219 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d29788, d69219, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d29788, d69219, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h20 (q : Pattern) (ha : d289022 q = 1) (hb : d289824 q = 1) : d0 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d289022, d289824, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d289022, d289824, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q hb ha
  exact h20 p ha hb
theorem andIntro74332 (p : Pattern) (ha : d289028 p = 1) (hb : d289830 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d289023 q = 1) (hb : d289825 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d289023, d289825, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro74331 q ha hb
    | true =>
      simp only [d289023, d289825, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d289024 q = 1) (hb : d289826 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d289024, d289826, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d289024, d289826, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d289025 q = 1) (hb : d289827 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d289025, d289827, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d289025, d289827, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d289026 q = 1) (hb : d289828 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d289026, d289828, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d289026, d289828, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d289027 q = 1) (hb : d289829 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d289027, d289829, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d289027, d289829, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d289028 q = 1) (hb : d289830 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d289028, d289830, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d289028, d289830, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro74333 (p : Pattern) (ha : d289034 p = 1) (hb : d289836 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d288922 q = 1) (hb : d289737 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d288922, d289737, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro74306 q ha hb
    | true =>
      simp only [d288922, d289737, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro74309 q ha hb
  have h2 (q : Pattern) (ha : d288923 q = 1) (hb : d289738 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d288923, d289738, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d288923, d289738, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d288924 q = 1) (hb : d289739 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d288924, d289739, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d288924, d289739, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d288927 q = 1) (hb : d289742 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d288927, d289742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro74309 q ha hb
    | true =>
      simp only [d288927, d289742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro74310 q ha hb
  have h5 (q : Pattern) (ha : d288928 q = 1) (hb : d289743 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d288928, d289743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d288928, d289743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d288929 q = 1) (hb : d289744 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d288929, d289744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d288929, d289744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d288930 q = 1) (hb : d289745 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d288930, d289745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d288930, d289745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d289029 q = 1) (hb : d289831 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d289029, d289831, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro74330 q ha hb
    | true =>
      simp only [d289029, d289831, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro74332 q ha hb
  have h9 (q : Pattern) (ha : d289030 q = 1) (hb : d289832 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d289030, d289832, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d289030, d289832, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d289031 q = 1) (hb : d289833 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d289031, d289833, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d289031, d289833, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d289032 q = 1) (hb : d289834 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d289032, d289834, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d289032, d289834, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d289033 q = 1) (hb : d289835 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d289033, d289835, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d289033, d289835, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d289034 q = 1) (hb : d289836 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d289034, d289836, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d289034, d289836, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h13 p ha hb
theorem andIntro74334 (p : Pattern) (ha : d289040 p = 1) (hb : d289842 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d289035 q = 1) (hb : d289837 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d289035, d289837, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro74333 q ha hb
    | true =>
      simp only [d289035, d289837, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d289036 q = 1) (hb : d289838 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d289036, d289838, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d289036, d289838, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d289037 q = 1) (hb : d289839 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d289037, d289839, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d289037, d289839, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d289038 q = 1) (hb : d289840 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d289038, d289840, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d289038, d289840, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d289039 q = 1) (hb : d289841 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d289039, d289841, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d289039, d289841, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d289040 q = 1) (hb : d289842 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d289040, d289842, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d289040, d289842, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro74335 (p : Pattern) (ha : d289046 p = 1) (hb : d289848 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d288971 q = 1) (hb : d289786 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d288971, d289786, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro74319 q ha hb
    | true =>
      simp only [d288971, d289786, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro74320 q ha hb
  have h2 (q : Pattern) (ha : d288972 q = 1) (hb : d289787 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d288972, d289787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d288972, d289787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d288973 q = 1) (hb : d289788 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d288973, d289788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d288973, d289788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d288974 q = 1) (hb : d289789 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d288974, d289789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d288974, d289789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d288981 q = 1) (hb : d289796 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d288981, d289796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro74321 q ha hb
    | true =>
      simp only [d288981, d289796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro74322 q ha hb
  have h6 (q : Pattern) (ha : d288982 q = 1) (hb : d289797 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d288982, d289797, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d288982, d289797, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d288983 q = 1) (hb : d289798 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d288983, d289798, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d288983, d289798, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d289013 q = 1) (hb : d289815 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d289013, d289815, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro74328 q ha hb
    | true =>
      simp only [d289013, d289815, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro74313 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d288948 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d289014 q = 1) (hb : d289816 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d289014, d289816, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d289014, d289816, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
  have h11 (q : Pattern) (ha : d289041 q = 1) (hb : d289843 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d289041, d289843, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro74334 q ha hb
    | true =>
      simp only [d289041, d289843, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d289042 q = 1) (hb : d289844 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d289042, d289844, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d289042, d289844, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d289043 q = 1) (hb : d289845 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d289043, d289845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d289043, d289845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d289044 q = 1) (hb : d289846 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d289044, d289846, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d289044, d289846, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d289045 q = 1) (hb : d289847 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d289045, d289847, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d289045, d289847, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d289046 q = 1) (hb : d289848 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d289046, d289848, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d289046, d289848, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  exact h16 p ha hb
theorem andIntro74336 (p : Pattern) (ha : d289047 p = 1) (hb : d289849 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d288934 q = 1) (hb : d289749 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d288934, d289749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro74311 q ha hb
    | true =>
      simp only [d288934, d289749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d288935 q = 1) (hb : d289750 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d288935, d289750, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d288935, d289750, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d288938 q = 1) (hb : d289753 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d288938, d289753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro74312 q ha hb
    | true =>
      simp only [d288938, d289753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d288939 q = 1) (hb : d289754 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d288939, d289754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d288939, d289754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d288940 q = 1) (hb : d289755 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d288940, d289755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d288940, d289755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d288941 q = 1) (hb : d289756 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d288941, d289756, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d288941, d289756, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d288967 q = 1) (hb : d289782 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d288967, d289782, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d288967, d289782, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d289047 q = 1) (hb : d289849 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d289047, d289849, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d289047, d289849, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro74337 (p : Pattern) (ha : d289048 p = 1) (hb : d289850 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d288938 q = 1) (hb : d289753 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d288938, d289753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro74312 q ha hb
    | true =>
      simp only [d288938, d289753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d288939 q = 1) (hb : d289754 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d288939, d289754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d288939, d289754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d288944 q = 1) (hb : d289759 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d288944, d289759, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d288944, d289759, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d288945 q = 1) (hb : d289760 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d288945, d289760, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d288945, d289760, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d288969 q = 1) (hb : d289784 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d288969, d289784, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d288969, d289784, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d289048 q = 1) (hb : d289850 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d289048, d289850, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d289048, d289850, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro74338 (p : Pattern) (ha : d289053 p = 1) (hb : d289855 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d288934 q = 1) (hb : d289749 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d288934, d289749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro74311 q ha hb
    | true =>
      simp only [d288934, d289749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d288935 q = 1) (hb : d289750 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d288935, d289750, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d288935, d289750, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d288938 q = 1) (hb : d289753 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d288938, d289753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro74312 q ha hb
    | true =>
      simp only [d288938, d289753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d288939 q = 1) (hb : d289754 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d288939, d289754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d288939, d289754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d288940 q = 1) (hb : d289755 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d288940, d289755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d288940, d289755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d288975 q = 1) (hb : d289790 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d288975, d289790, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d288975, d289790, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d288976 q = 1) (hb : d289791 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d288976, d289791, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d288976, d289791, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d289053 q = 1) (hb : d289855 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d289053, d289855, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d289053, d289855, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro74339 (p : Pattern) (ha : d289054 p = 1) (hb : d289856 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d288938 q = 1) (hb : d289753 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d288938, d289753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro74312 q ha hb
    | true =>
      simp only [d288938, d289753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d288939 q = 1) (hb : d289754 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d288939, d289754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d288939, d289754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d288944 q = 1) (hb : d289759 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d288944, d289759, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d288944, d289759, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d288978 q = 1) (hb : d289793 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d288978, d289793, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d288978, d289793, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d288979 q = 1) (hb : d289794 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d288979, d289794, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d288979, d289794, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d289054 q = 1) (hb : d289856 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d289054, d289856, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d289054, d289856, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro74340 (p : Pattern) (ha : d289058 p = 1) (hb : d289860 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d289007 q = 1) (hb : d289809 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d289007, d289809, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro74327 q ha hb
    | true =>
      simp only [d289007, d289809, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d289008 q = 1) (hb : d289810 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d289008, d289810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d289008, d289810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d288934 q = 1) (hb : d289749 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d288934, d289749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro74311 q ha hb
    | true =>
      simp only [d288934, d289749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d288935 q = 1) (hb : d289750 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d288935, d289750, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d288935, d289750, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d289009 q = 1) (hb : d289811 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d289009, d289811, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d289009, d289811, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d289010 q = 1) (hb : d289812 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d289010, d289812, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d289010, d289812, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d289011 q = 1) (hb : d289813 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d289011, d289813, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d289011, d289813, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d289058 q = 1) (hb : d289860 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d289058, d289860, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d289058, d289860, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro74341 (p : Pattern) (ha : d289061 p = 1) (hb : d289863 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d289035 q = 1) (hb : d289837 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d289035, d289837, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro74333 q ha hb
    | true =>
      simp only [d289035, d289837, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d289036 q = 1) (hb : d289838 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d289036, d289838, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d289036, d289838, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d289037 q = 1) (hb : d289839 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d289037, d289839, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d289037, d289839, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d289038 q = 1) (hb : d289840 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d289038, d289840, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d289038, d289840, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d289039 q = 1) (hb : d289841 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d289039, d289841, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d289039, d289841, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d289061 q = 1) (hb : d289863 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d289061, d289863, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d289061, d289863, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro74342 (p : Pattern) (ha : d289067 p = 1) (hb : d289869 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d288971 q = 1) (hb : d289786 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d288971, d289786, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro74319 q ha hb
    | true =>
      simp only [d288971, d289786, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro74320 q ha hb
  have h2 (q : Pattern) (ha : d288972 q = 1) (hb : d289787 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d288972, d289787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d288972, d289787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d288973 q = 1) (hb : d289788 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d288973, d289788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d288973, d289788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d288974 q = 1) (hb : d289789 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d288974, d289789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d288974, d289789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d288981 q = 1) (hb : d289796 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d288981, d289796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro74321 q ha hb
    | true =>
      simp only [d288981, d289796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro74322 q ha hb
  have h6 (q : Pattern) (ha : d288982 q = 1) (hb : d289797 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d288982, d289797, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d288982, d289797, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d288983 q = 1) (hb : d289798 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d288983, d289798, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d288983, d289798, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d289013 q = 1) (hb : d289815 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d289013, d289815, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro74328 q ha hb
    | true =>
      simp only [d289013, d289815, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro74313 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d288948 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d289014 q = 1) (hb : d289816 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d289014, d289816, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d289014, d289816, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
  have h11 (q : Pattern) (ha : d289041 q = 1) (hb : d289843 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d289041, d289843, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro74334 q ha hb
    | true =>
      simp only [d289041, d289843, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d289042 q = 1) (hb : d289844 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d289042, d289844, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d289042, d289844, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d289043 q = 1) (hb : d289845 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d289043, d289845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d289043, d289845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d289044 q = 1) (hb : d289846 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d289044, d289846, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d289044, d289846, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d289045 q = 1) (hb : d289847 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d289045, d289847, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d289045, d289847, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d289049 q = 1) (hb : d289851 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d289049, d289851, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro74336 q ha hb
    | true =>
      simp only [d289049, d289851, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro74337 q ha hb
  have h17 (q : Pattern) (ha : d289050 q = 1) (hb : d289852 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d289050, d289852, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d289050, d289852, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d289051 q = 1) (hb : d289853 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d289051, d289853, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d289051, d289853, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h19 (q : Pattern) (ha : d289052 q = 1) (hb : d289854 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d289052, d289854, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d289052, d289854, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d289055 q = 1) (hb : d289857 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d289055, d289857, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro74338 q ha hb
    | true =>
      simp only [d289055, d289857, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro74339 q ha hb
  have h21 (q : Pattern) (ha : d289056 q = 1) (hb : d289858 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d289056, d289858, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d289056, d289858, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
  have h22 (q : Pattern) (ha : d289057 q = 1) (hb : d289859 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d289057, d289859, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d289057, d289859, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h23 (q : Pattern) (ha : d289059 q = 1) (hb : d289861 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d289059, d289861, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro74340 q ha hb
    | true =>
      simp only [d289059, d289861, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro74316 q ha hb
  have h24 (q : Pattern) (ha : d0 q = 1) (hb : d288958 q = 1) : d0 q = 1 := by
    exact ha
  have h25 (q : Pattern) (ha : d289060 q = 1) (hb : d289862 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d289060, d289862, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
    | true =>
      simp only [d289060, d289862, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q hb ha
  have h26 (q : Pattern) (ha : d289062 q = 1) (hb : d289864 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d289062, d289864, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro74341 q ha hb
    | true =>
      simp only [d289062, d289864, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h27 (q : Pattern) (ha : d289063 q = 1) (hb : d289865 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d289063, d289865, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h26 q ha hb
    | true =>
      simp only [d289063, d289865, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h28 (q : Pattern) (ha : d289064 q = 1) (hb : d289866 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d289064, d289866, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q ha hb
    | true =>
      simp only [d289064, d289866, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h27 q ha hb
  have h29 (q : Pattern) (ha : d289065 q = 1) (hb : d289867 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d289065, d289867, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
    | true =>
      simp only [d289065, d289867, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h28 q ha hb
  have h30 (q : Pattern) (ha : d289066 q = 1) (hb : d289868 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d289066, d289868, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d289066, d289868, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h29 q ha hb
  have h31 (q : Pattern) (ha : d289067 q = 1) (hb : d289869 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d289067, d289869, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d289067, d289869, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h30 q ha hb
  exact h31 p ha hb
theorem andIntro74343 (p : Pattern) (ha : d289074 p = 1) (hb : d289876 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d288948 q = 1) (hb : d289763 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d288948, d289763, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro74313 q ha hb
    | true =>
      simp only [d288948, d289763, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro74314 q ha hb
  have h2 (q : Pattern) (ha : d288949 q = 1) (hb : d289764 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d288949, d289764, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d288949, d289764, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d288950 q = 1) (hb : d289765 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d288950, d289765, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d288950, d289765, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d288951 q = 1) (hb : d289766 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d288951, d289766, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d288951, d289766, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d288952 q = 1) (hb : d289767 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d288952, d289767, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d288952, d289767, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d289069 q = 1) (hb : d289871 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d289069, d289871, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro74314 q ha hb
    | true =>
      simp only [d289069, d289871, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d289070 q = 1) (hb : d289872 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d289070, d289872, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d289070, d289872, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d289071 q = 1) (hb : d289873 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d289071, d289873, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d289071, d289873, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d289072 q = 1) (hb : d289874 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d289072, d289874, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d289072, d289874, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d289073 q = 1) (hb : d289875 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d289073, d289875, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d289073, d289875, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d289074 q = 1) (hb : d289876 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d289074, d289876, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d289074, d289876, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro74344 (p : Pattern) (ha : d289080 p = 1) (hb : d289882 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d289069 q = 1) (hb : d289871 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d289069, d289871, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro74314 q ha hb
    | true =>
      simp only [d289069, d289871, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d289070 q = 1) (hb : d289872 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d289070, d289872, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d289070, d289872, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d289071 q = 1) (hb : d289873 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d289071, d289873, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d289071, d289873, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d289072 q = 1) (hb : d289874 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d289072, d289874, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d289072, d289874, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d289073 q = 1) (hb : d289875 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d289073, d289875, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d289073, d289875, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d289075 q = 1) (hb : d289877 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d289075, d289877, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro74317 q ha hb
    | true =>
      simp only [d289075, d289877, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d289076 q = 1) (hb : d289878 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d289076, d289878, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d289076, d289878, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d289077 q = 1) (hb : d289879 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d289077, d289879, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d289077, d289879, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d289078 q = 1) (hb : d289880 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d289078, d289880, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d289078, d289880, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d289079 q = 1) (hb : d289881 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d289079, d289881, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d289079, d289881, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d289080 q = 1) (hb : d289882 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d289080, d289882, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d289080, d289882, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro74345 (p : Pattern) (ha : d289087 p = 1) (hb : d289889 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d289059 q = 1) (hb : d289861 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d289059, d289861, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro74340 q ha hb
    | true =>
      simp only [d289059, d289861, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro74316 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d288958 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d289060 q = 1) (hb : d289862 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d289060, d289862, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d289060, d289862, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d289062 q = 1) (hb : d289864 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d289062, d289864, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro74341 q ha hb
    | true =>
      simp only [d289062, d289864, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d289063 q = 1) (hb : d289865 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d289063, d289865, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d289063, d289865, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d289064 q = 1) (hb : d289866 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d289064, d289866, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d289064, d289866, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d289085 q = 1) (hb : d289887 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d289085, d289887, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d289085, d289887, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d289086 q = 1) (hb : d289888 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d289086, d289888, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d289086, d289888, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d289087 q = 1) (hb : d289889 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d289087, d289889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d289087, d289889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro74346 (p : Pattern) (ha : d289089 p = 1) (hb : d289891 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d289075 q = 1) (hb : d289877 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d289075, d289877, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro74317 q ha hb
    | true =>
      simp only [d289075, d289877, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d289076 q = 1) (hb : d289878 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d289076, d289878, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d289076, d289878, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d289077 q = 1) (hb : d289879 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d289077, d289879, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d289077, d289879, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d289078 q = 1) (hb : d289880 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d289078, d289880, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d289078, d289880, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d289079 q = 1) (hb : d289881 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d289079, d289881, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d289079, d289881, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d289089 q = 1) (hb : d289891 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d289089, d289891, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d289089, d289891, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro74347 (p : Pattern) (ha : d42021 p = 1) (hb : d289109 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d42007 q = 1) (hb : d289095 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d42007, d289095, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d42007, d289095, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro74323 q ha hb
  have h2 (q : Pattern) (ha : d41793 q = 1) (hb : d288985 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d41793, d288985, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro74323 q ha hb
    | true =>
      simp only [d41793, d288985, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d42008 q = 1) (hb : d289096 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d42008, d289096, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d42008, d289096, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d41794 q = 1) (hb : d288986 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d41794, d288986, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d41794, d288986, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d42009 q = 1) (hb : d289097 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d42009, d289097, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d42009, d289097, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d42010 q = 1) (hb : d289098 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d42010, d289098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d42010, d289098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d42011 q = 1) (hb : d289099 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d42011, d289099, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d42011, d289099, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro74324 q ha hb
  have h8 (q : Pattern) (ha : d41798 q = 1) (hb : d288990 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d41798, d288990, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro74324 q ha hb
    | true =>
      simp only [d41798, d288990, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d42012 q = 1) (hb : d289100 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d42012, d289100, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d42012, d289100, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d41799 q = 1) (hb : d288991 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d41799, d288991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d41799, d288991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d42013 q = 1) (hb : d289101 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d42013, d289101, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d42013, d289101, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d42014 q = 1) (hb : d289102 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d42014, d289102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d42014, d289102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d42015 q = 1) (hb : d289103 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d42015, d289103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d42015, d289103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d42016 q = 1) (hb : d289104 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d42016, d289104, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d42016, d289104, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro74302 q ha hb
  have h15 (q : Pattern) (ha : d41696 q = 1) (hb : d288888 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d41696, d288888, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro74302 q ha hb
    | true =>
      simp only [d41696, d288888, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h16 (q : Pattern) (ha : d42017 q = 1) (hb : d289105 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d42017, d289105, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d42017, d289105, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d41697 q = 1) (hb : d288889 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d41697, d288889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d41697, d288889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h18 (q : Pattern) (ha : d42018 q = 1) (hb : d289106 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d42018, d289106, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d42018, d289106, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d42019 q = 1) (hb : d289107 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d42019, d289107, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d42019, d289107, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h20 (q : Pattern) (ha : d42020 q = 1) (hb : d289108 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d42020, d289108, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d42020, d289108, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
  have h21 (q : Pattern) (ha : d42021 q = 1) (hb : d289109 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d42021, d289109, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d42021, d289109, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
  exact h21 p ha hb
theorem andIntro74348 (p : Pattern) (ha : d289124 p = 1) (hb : d289911 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d289110 q = 1) (hb : d289897 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d289110, d289897, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d289110, d289897, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro74303 q ha hb
  have h2 (q : Pattern) (ha : d288866 q = 1) (hb : d289701 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d288866, d289701, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro74303 q ha hb
    | true =>
      simp only [d288866, d289701, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d289111 q = 1) (hb : d289898 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d289111, d289898, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d289111, d289898, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d288867 q = 1) (hb : d289702 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d288867, d289702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d288867, d289702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d289112 q = 1) (hb : d289899 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d289112, d289899, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d289112, d289899, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d289113 q = 1) (hb : d289900 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d289113, d289900, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d289113, d289900, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d289114 q = 1) (hb : d289901 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d289114, d289901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d289114, d289901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro74304 q ha hb
  have h8 (q : Pattern) (ha : d288879 q = 1) (hb : d289708 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d288879, d289708, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro74304 q ha hb
    | true =>
      simp only [d288879, d289708, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d289115 q = 1) (hb : d289902 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d289115, d289902, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d289115, d289902, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d288880 q = 1) (hb : d289709 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d288880, d289709, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d288880, d289709, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h11 (q : Pattern) (ha : d289116 q = 1) (hb : d289903 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d289116, d289903, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d289116, d289903, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d289117 q = 1) (hb : d289904 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d289117, d289904, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d289117, d289904, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d289118 q = 1) (hb : d289905 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d289118, d289905, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d289118, d289905, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d42016 q = 1) (hb : d289104 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d42016, d289104, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d42016, d289104, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro74302 q ha hb
  have h15 (q : Pattern) (ha : d41696 q = 1) (hb : d288888 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d41696, d288888, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro74302 q ha hb
    | true =>
      simp only [d41696, d288888, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h16 (q : Pattern) (ha : d42017 q = 1) (hb : d289105 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d42017, d289105, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d42017, d289105, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d41697 q = 1) (hb : d288889 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d41697, d288889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d41697, d288889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h18 (q : Pattern) (ha : d42018 q = 1) (hb : d289106 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d42018, d289106, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d42018, d289106, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d42019 q = 1) (hb : d289107 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d42019, d289107, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d42019, d289107, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h20 (q : Pattern) (ha : d289119 q = 1) (hb : d289906 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d289119, d289906, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d289119, d289906, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro74305 q ha hb
  have h21 (q : Pattern) (ha : d288897 q = 1) (hb : d289716 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d288897, d289716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro74305 q ha hb
    | true =>
      simp only [d288897, d289716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h22 (q : Pattern) (ha : d289120 q = 1) (hb : d289907 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d289120, d289907, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d289120, d289907, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
  have h23 (q : Pattern) (ha : d288898 q = 1) (hb : d289717 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d288898, d289717, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d288898, d289717, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h24 (q : Pattern) (ha : d289121 q = 1) (hb : d289908 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d289121, d289908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
    | true =>
      simp only [d289121, d289908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
  have h25 (q : Pattern) (ha : d289122 q = 1) (hb : d289909 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d289122, d289909, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q ha hb
    | true =>
      simp only [d289122, d289909, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h26 (q : Pattern) (ha : d289123 q = 1) (hb : d289910 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d289123, d289910, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q hb ha
    | true =>
      simp only [d289123, d289910, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q ha hb
  have h27 (q : Pattern) (ha : d289124 q = 1) (hb : d289911 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d289124, d289911, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d289124, d289911, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h26 q ha hb
  exact h27 p ha hb
theorem andIntro74349 (p : Pattern) (ha : d289129 p = 1) (hb : d289916 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d42016 q = 1) (hb : d289104 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d42016, d289104, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d42016, d289104, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro74302 q ha hb
  have h2 (q : Pattern) (ha : d41696 q = 1) (hb : d288888 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d41696, d288888, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro74302 q ha hb
    | true =>
      simp only [d41696, d288888, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d42017 q = 1) (hb : d289105 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d42017, d289105, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d42017, d289105, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d41697 q = 1) (hb : d288889 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d41697, d288889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d41697, d288889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d42018 q = 1) (hb : d289106 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d42018, d289106, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d42018, d289106, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d42019 q = 1) (hb : d289107 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d42019, d289107, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d42019, d289107, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d289119 q = 1) (hb : d289906 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d289119, d289906, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d289119, d289906, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro74305 q ha hb
  have h8 (q : Pattern) (ha : d288897 q = 1) (hb : d289716 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d288897, d289716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro74305 q ha hb
    | true =>
      simp only [d288897, d289716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d289120 q = 1) (hb : d289907 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d289120, d289907, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d289120, d289907, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d288898 q = 1) (hb : d289717 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d288898, d289717, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d288898, d289717, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h11 (q : Pattern) (ha : d289121 q = 1) (hb : d289908 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d289121, d289908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d289121, d289908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d289122 q = 1) (hb : d289909 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d289122, d289909, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d289122, d289909, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d289123 q = 1) (hb : d289910 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d289123, d289910, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
    | true =>
      simp only [d289123, d289910, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d289128 q = 1) (hb : d289915 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d289128, d289915, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d289128, d289915, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h15 (q : Pattern) (ha : d289129 q = 1) (hb : d289916 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d289129, d289916, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d289129, d289916, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro74350 (p : Pattern) (ha : d289143 p = 1) (hb : d289930 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d289134 q = 1) (hb : d289921 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d289134, d289921, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d289134, d289921, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro74307 q ha hb
  have h2 (q : Pattern) (ha : d288910 q = 1) (hb : d289725 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d288910, d289725, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro74307 q ha hb
    | true =>
      simp only [d288910, d289725, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d289135 q = 1) (hb : d289922 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d289135, d289922, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d289135, d289922, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d288911 q = 1) (hb : d289726 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d288911, d289726, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d288911, d289726, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d289136 q = 1) (hb : d289923 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d289136, d289923, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d289136, d289923, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d289137 q = 1) (hb : d289924 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d289137, d289924, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d289137, d289924, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d289138 q = 1) (hb : d289925 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d289138, d289925, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d289138, d289925, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro74308 q ha hb
  have h8 (q : Pattern) (ha : d288915 q = 1) (hb : d289730 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d288915, d289730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro74308 q ha hb
    | true =>
      simp only [d288915, d289730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d289139 q = 1) (hb : d289926 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d289139, d289926, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d289139, d289926, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d288916 q = 1) (hb : d289731 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d288916, d289731, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d288916, d289731, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h11 (q : Pattern) (ha : d289140 q = 1) (hb : d289927 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d289140, d289927, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d289140, d289927, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d289141 q = 1) (hb : d289928 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d289141, d289928, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d289141, d289928, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d289142 q = 1) (hb : d289929 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d289142, d289929, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d289142, d289929, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d289119 q = 1) (hb : d289906 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d289119, d289906, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d289119, d289906, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro74305 q ha hb
  have h15 (q : Pattern) (ha : d288897 q = 1) (hb : d289716 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d288897, d289716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro74305 q ha hb
    | true =>
      simp only [d288897, d289716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h16 (q : Pattern) (ha : d289120 q = 1) (hb : d289907 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d289120, d289907, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d289120, d289907, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d288898 q = 1) (hb : d289717 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d288898, d289717, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d288898, d289717, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h18 (q : Pattern) (ha : d289121 q = 1) (hb : d289908 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d289121, d289908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d289121, d289908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d289122 q = 1) (hb : d289909 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d289122, d289909, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d289122, d289909, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h20 (q : Pattern) (ha : d289128 q = 1) (hb : d289915 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d289128, d289915, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d289128, d289915, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h21 (q : Pattern) (ha : d289143 q = 1) (hb : d289930 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d289143, d289930, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d289143, d289930, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
  exact h21 p ha hb
theorem andIntro74351 (p : Pattern) (ha : d289148 p = 1) (hb : d289935 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d289138 q = 1) (hb : d289925 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d289138, d289925, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d289138, d289925, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro74308 q ha hb
  have h2 (q : Pattern) (ha : d288915 q = 1) (hb : d289730 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d288915, d289730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro74308 q ha hb
    | true =>
      simp only [d288915, d289730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d289139 q = 1) (hb : d289926 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d289139, d289926, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d289139, d289926, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d288916 q = 1) (hb : d289731 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d288916, d289731, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d288916, d289731, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d289140 q = 1) (hb : d289927 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d289140, d289927, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d289140, d289927, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d289141 q = 1) (hb : d289928 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d289141, d289928, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d289141, d289928, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d289147 q = 1) (hb : d289934 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d289147, d289934, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d289147, d289934, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d29925 q = 1) (hb : d123451 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d29925, d123451, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d29925, d123451, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro71084 q ha hb
  have h9 (q : Pattern) (ha : d29596 q = 1) (hb : d101562 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d29596, d101562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro71084 q ha hb
    | true =>
      simp only [d29596, d101562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d29926 q = 1) (hb : d123452 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d29926, d123452, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d29926, d123452, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d29597 q = 1) (hb : d101564 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d29597, d101564, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d29597, d101564, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d29927 q = 1) (hb : d123453 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d29927, d123453, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d29927, d123453, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d29928 q = 1) (hb : d123454 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d29928, d123454, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d29928, d123454, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d29929 q = 1) (hb : d123455 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d29929, d123455, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d29929, d123455, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d289148 q = 1) (hb : d289935 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d289148, d289935, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d289148, d289935, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  exact h15 p ha hb
theorem andIntro74352 (p : Pattern) (ha : d289154 p = 1) (hb : d289941 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d289125 q = 1) (hb : d289912 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d289125, d289912, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro74347 q hb ha
    | true =>
      simp only [d289125, d289912, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro74348 q ha hb
  have h2 (q : Pattern) (ha : d289126 q = 1) (hb : d289913 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d289126, d289913, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d289126, d289913, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d289127 q = 1) (hb : d289914 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d289127, d289914, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d289127, d289914, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d289130 q = 1) (hb : d289917 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d289130, d289917, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro74348 q ha hb
    | true =>
      simp only [d289130, d289917, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro74349 q ha hb
  have h5 (q : Pattern) (ha : d289131 q = 1) (hb : d289918 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d289131, d289918, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d289131, d289918, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d289132 q = 1) (hb : d289919 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d289132, d289919, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d289132, d289919, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d289133 q = 1) (hb : d289920 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d289133, d289920, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d289133, d289920, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d289144 q = 1) (hb : d289931 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d289144, d289931, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro74348 q ha hb
    | true =>
      simp only [d289144, d289931, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro74350 q ha hb
  have h9 (q : Pattern) (ha : d289145 q = 1) (hb : d289932 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d289145, d289932, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d289145, d289932, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d289146 q = 1) (hb : d289933 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d289146, d289933, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d289146, d289933, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d289149 q = 1) (hb : d289936 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d289149, d289936, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro74350 q ha hb
    | true =>
      simp only [d289149, d289936, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro74351 q ha hb
  have h12 (q : Pattern) (ha : d289150 q = 1) (hb : d289937 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d289150, d289937, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d289150, d289937, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d289151 q = 1) (hb : d289938 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d289151, d289938, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d289151, d289938, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d289152 q = 1) (hb : d289939 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d289152, d289939, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d289152, d289939, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d289153 q = 1) (hb : d289940 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d289153, d289940, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d289153, d289940, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d289154 q = 1) (hb : d289941 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d289154, d289941, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d289154, d289941, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h16 p ha hb
theorem andIntro74353 (p : Pattern) (ha : d289159 p = 1) (hb : d289946 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d289144 q = 1) (hb : d289931 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d289144, d289931, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro74348 q ha hb
    | true =>
      simp only [d289144, d289931, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro74350 q ha hb
  have h2 (q : Pattern) (ha : d289145 q = 1) (hb : d289932 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d289145, d289932, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d289145, d289932, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d289146 q = 1) (hb : d289933 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d289146, d289933, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d289146, d289933, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d289149 q = 1) (hb : d289936 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d289149, d289936, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro74350 q ha hb
    | true =>
      simp only [d289149, d289936, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro74351 q ha hb
  have h5 (q : Pattern) (ha : d289150 q = 1) (hb : d289937 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d289150, d289937, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d289150, d289937, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d289151 q = 1) (hb : d289938 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d289151, d289938, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d289151, d289938, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d289152 q = 1) (hb : d289939 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d289152, d289939, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d289152, d289939, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d289157 q = 1) (hb : d289944 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d289157, d289944, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d289157, d289944, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d289158 q = 1) (hb : d289945 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d289158, d289945, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d289158, d289945, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d289159 q = 1) (hb : d289946 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d289159, d289946, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d289159, d289946, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h10 p ha hb
theorem andIntro74354 (p : Pattern) (ha : d289165 p = 1) (hb : d289952 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d289155 q = 1) (hb : d289942 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d289155, d289942, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro74352 q ha hb
    | true =>
      simp only [d289155, d289942, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d289156 q = 1) (hb : d289943 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d289156, d289943, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d289156, d289943, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d289160 q = 1) (hb : d289947 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d289160, d289947, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro74353 q ha hb
    | true =>
      simp only [d289160, d289947, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d289161 q = 1) (hb : d289948 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d289161, d289948, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d289161, d289948, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d289162 q = 1) (hb : d289949 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d289162, d289949, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d289162, d289949, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d289163 q = 1) (hb : d289950 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d289163, d289950, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d289163, d289950, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d289164 q = 1) (hb : d289951 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d289164, d289951, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d289164, d289951, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d289165 q = 1) (hb : d289952 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d289165, d289952, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d289165, d289952, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro74355 (p : Pattern) (ha : d289167 p = 1) (hb : d289954 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d289149 q = 1) (hb : d289936 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d289149, d289936, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro74350 q ha hb
    | true =>
      simp only [d289149, d289936, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro74351 q ha hb
  have h2 (q : Pattern) (ha : d289150 q = 1) (hb : d289937 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d289150, d289937, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d289150, d289937, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d289151 q = 1) (hb : d289938 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d289151, d289938, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d289151, d289938, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d289157 q = 1) (hb : d289944 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d289157, d289944, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d289157, d289944, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d289166 q = 1) (hb : d289953 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d289166, d289953, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d289166, d289953, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d289167 q = 1) (hb : d289954 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d289167, d289954, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d289167, d289954, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro74356 (p : Pattern) (ha : d289173 p = 1) (hb : d289960 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d289160 q = 1) (hb : d289947 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d289160, d289947, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro74353 q ha hb
    | true =>
      simp only [d289160, d289947, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d289161 q = 1) (hb : d289948 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d289161, d289948, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d289161, d289948, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d289168 q = 1) (hb : d289955 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d289168, d289955, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro74355 q ha hb
    | true =>
      simp only [d289168, d289955, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d289169 q = 1) (hb : d289956 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d289169, d289956, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d289169, d289956, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d289170 q = 1) (hb : d289957 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d289170, d289957, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d289170, d289957, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d289171 q = 1) (hb : d289958 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d289171, d289958, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d289171, d289958, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d289172 q = 1) (hb : d289959 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d289172, d289959, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d289172, d289959, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d289173 q = 1) (hb : d289960 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d289173, d289960, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d289173, d289960, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro74357 (p : Pattern) (ha : d289186 p = 1) (hb : d289968 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d289134 q = 1) (hb : d289921 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d289134, d289921, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d289134, d289921, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro74307 q ha hb
  have h2 (q : Pattern) (ha : d288910 q = 1) (hb : d289725 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d288910, d289725, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro74307 q ha hb
    | true =>
      simp only [d288910, d289725, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d289135 q = 1) (hb : d289922 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d289135, d289922, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d289135, d289922, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d288911 q = 1) (hb : d289726 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d288911, d289726, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d288911, d289726, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d289136 q = 1) (hb : d289923 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d289136, d289923, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d289136, d289923, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d289137 q = 1) (hb : d289924 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d289137, d289924, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d289137, d289924, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d289138 q = 1) (hb : d289925 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d289138, d289925, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d289138, d289925, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro74308 q ha hb
  have h8 (q : Pattern) (ha : d288915 q = 1) (hb : d289730 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d288915, d289730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro74308 q ha hb
    | true =>
      simp only [d288915, d289730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d289139 q = 1) (hb : d289926 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d289139, d289926, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d289139, d289926, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d288916 q = 1) (hb : d289731 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d288916, d289731, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d288916, d289731, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h11 (q : Pattern) (ha : d289140 q = 1) (hb : d289927 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d289140, d289927, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d289140, d289927, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d289141 q = 1) (hb : d289928 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d289141, d289928, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d289141, d289928, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d289142 q = 1) (hb : d289929 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d289142, d289929, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d289142, d289929, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d289181 q = 1) (hb : d289963 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d289181, d289963, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d289181, d289963, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro74329 q ha hb
  have h15 (q : Pattern) (ha : d289016 q = 1) (hb : d289818 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d289016, d289818, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro74329 q ha hb
    | true =>
      simp only [d289016, d289818, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h16 (q : Pattern) (ha : d289182 q = 1) (hb : d289964 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d289182, d289964, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d289182, d289964, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d289017 q = 1) (hb : d289819 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d289017, d289819, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d289017, d289819, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h18 (q : Pattern) (ha : d289183 q = 1) (hb : d289965 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d289183, d289965, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d289183, d289965, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d289184 q = 1) (hb : d289966 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d289184, d289966, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d289184, d289966, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h20 (q : Pattern) (ha : d289185 q = 1) (hb : d289967 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d289185, d289967, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d289185, d289967, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h21 (q : Pattern) (ha : d289186 q = 1) (hb : d289968 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d289186, d289968, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d289186, d289968, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
  exact h21 p ha hb
theorem andIntro74358 (p : Pattern) (ha : d289192 p = 1) (hb : d289974 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d289187 q = 1) (hb : d289969 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d289187, d289969, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d289187, d289969, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro74331 q ha hb
  have h2 (q : Pattern) (ha : d289023 q = 1) (hb : d289825 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d289023, d289825, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro74331 q ha hb
    | true =>
      simp only [d289023, d289825, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d289188 q = 1) (hb : d289970 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d289188, d289970, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d289188, d289970, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d289024 q = 1) (hb : d289826 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d289024, d289826, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d289024, d289826, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d289189 q = 1) (hb : d289971 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d289189, d289971, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d289189, d289971, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d289190 q = 1) (hb : d289972 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d289190, d289972, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d289190, d289972, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d289191 q = 1) (hb : d289973 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d289191, d289973, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d289191, d289973, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d289192 q = 1) (hb : d289974 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d289192, d289974, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d289192, d289974, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro74359 (p : Pattern) (ha : d289198 p = 1) (hb : d289980 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d289144 q = 1) (hb : d289931 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d289144, d289931, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro74348 q ha hb
    | true =>
      simp only [d289144, d289931, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro74350 q ha hb
  have h2 (q : Pattern) (ha : d289145 q = 1) (hb : d289932 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d289145, d289932, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d289145, d289932, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d289146 q = 1) (hb : d289933 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d289146, d289933, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d289146, d289933, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d289149 q = 1) (hb : d289936 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d289149, d289936, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro74350 q ha hb
    | true =>
      simp only [d289149, d289936, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro74351 q ha hb
  have h5 (q : Pattern) (ha : d289150 q = 1) (hb : d289937 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d289150, d289937, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d289150, d289937, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d289151 q = 1) (hb : d289938 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d289151, d289938, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d289151, d289938, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d289152 q = 1) (hb : d289939 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d289152, d289939, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d289152, d289939, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d289193 q = 1) (hb : d289975 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d289193, d289975, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro74357 q ha hb
    | true =>
      simp only [d289193, d289975, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro74358 q ha hb
  have h9 (q : Pattern) (ha : d289194 q = 1) (hb : d289976 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d289194, d289976, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d289194, d289976, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d289195 q = 1) (hb : d289977 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d289195, d289977, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d289195, d289977, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d289196 q = 1) (hb : d289978 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d289196, d289978, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d289196, d289978, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d289197 q = 1) (hb : d289979 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d289197, d289979, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d289197, d289979, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d289198 q = 1) (hb : d289980 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d289198, d289980, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d289198, d289980, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h13 p ha hb
theorem andIntro74360 (p : Pattern) (ha : d289204 p = 1) (hb : d289986 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d289199 q = 1) (hb : d289981 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d289199, d289981, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro74359 q ha hb
    | true =>
      simp only [d289199, d289981, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d289200 q = 1) (hb : d289982 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d289200, d289982, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d289200, d289982, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d289201 q = 1) (hb : d289983 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d289201, d289983, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d289201, d289983, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d289202 q = 1) (hb : d289984 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d289202, d289984, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d289202, d289984, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d289203 q = 1) (hb : d289985 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d289203, d289985, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d289203, d289985, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d289204 q = 1) (hb : d289986 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d289204, d289986, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d289204, d289986, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro74361 (p : Pattern) (ha : d289210 p = 1) (hb : d289992 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d289174 q = 1) (hb : d289961 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d289174, d289961, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro74354 q ha hb
    | true =>
      simp only [d289174, d289961, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro74356 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d289179 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d289180 q = 1) (hb : d289962 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d289180, d289962, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d289180, d289962, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d289205 q = 1) (hb : d289987 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d289205, d289987, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro74360 q ha hb
    | true =>
      simp only [d289205, d289987, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d289206 q = 1) (hb : d289988 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d289206, d289988, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d289206, d289988, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d289207 q = 1) (hb : d289989 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d289207, d289989, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d289207, d289989, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d289208 q = 1) (hb : d289990 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d289208, d289990, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d289208, d289990, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d289209 q = 1) (hb : d289991 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d289209, d289991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d289209, d289991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d289210 q = 1) (hb : d289992 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d289210, d289992, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d289210, d289992, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro74362 (p : Pattern) (ha : d289178 p = 1) (hb : d289997 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d289168 q = 1) (hb : d289955 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d289168, d289955, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro74355 q ha hb
    | true =>
      simp only [d289168, d289955, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d289169 q = 1) (hb : d289956 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d289169, d289956, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d289169, d289956, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d289175 q = 1) (hb : d289994 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d289175, d289994, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d289175, d289994, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d289176 q = 1) (hb : d289995 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d289176, d289995, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d289176, d289995, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d289177 q = 1) (hb : d289996 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d289177, d289996, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d289177, d289996, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d289178 q = 1) (hb : d289997 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d289178, d289997, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d289178, d289997, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro74363 (p : Pattern) (ha : d289217 p = 1) (hb : d290003 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d289212 q = 1) (hb : d289998 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d289212, d289998, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro74362 q ha hb
    | true =>
      simp only [d289212, d289998, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d289213 q = 1) (hb : d289999 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d289213, d289999, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d289213, d289999, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d289214 q = 1) (hb : d290000 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d289214, d290000, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d289214, d290000, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d289215 q = 1) (hb : d290001 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d289215, d290001, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d289215, d290001, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d289216 q = 1) (hb : d290002 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d289216, d290002, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d289216, d290002, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d289217 q = 1) (hb : d290003 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d289217, d290003, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d289217, d290003, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro74364 (p : Pattern) (ha : d289223 p = 1) (hb : d290009 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d288954 q = 1) (hb : d289769 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d288954, d289769, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d288954, d289769, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro74315 q ha hb
  have h2 (q : Pattern) (ha : d288955 q = 1) (hb : d289770 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d288955, d289770, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d288955, d289770, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d288964 q = 1) (hb : d289779 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d288964, d289779, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro74315 q ha hb
    | true =>
      simp only [d288964, d289779, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro74318 q ha hb
  have h4 (q : Pattern) (ha : d288965 q = 1) (hb : d289780 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d288965, d289780, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d288965, d289780, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d288966 q = 1) (hb : d289781 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d288966, d289781, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d288966, d289781, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d289068 q = 1) (hb : d289870 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d289068, d289870, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro74335 q ha hb
    | true =>
      simp only [d289068, d289870, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro74342 q ha hb
  have h7 (q : Pattern) (ha : d289081 q = 1) (hb : d289883 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d289081, d289883, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro74343 q ha hb
    | true =>
      simp only [d289081, d289883, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro74344 q ha hb
  have h8 (q : Pattern) (ha : d289082 q = 1) (hb : d289884 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d289082, d289884, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d289082, d289884, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d289083 q = 1) (hb : d289885 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d289083, d289885, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d289083, d289885, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h10 (q : Pattern) (ha : d289084 q = 1) (hb : d289886 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d289084, d289886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d289084, d289886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d289088 q = 1) (hb : d289890 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d289088, d289890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d289088, d289890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro74345 q ha hb
  have h12 (q : Pattern) (ha : d289090 q = 1) (hb : d289892 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d289090, d289892, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d289090, d289892, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro74346 q ha hb
  have h13 (q : Pattern) (ha : d289091 q = 1) (hb : d289893 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d289091, d289893, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d289091, d289893, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d289092 q = 1) (hb : d289894 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d289092, d289894, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d289092, d289894, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h15 (q : Pattern) (ha : d289093 q = 1) (hb : d289895 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d289093, d289895, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d289093, d289895, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h16 (q : Pattern) (ha : d289094 q = 1) (hb : d289896 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d289094, d289896, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d289094, d289896, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d289211 q = 1) (hb : d289993 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d289211, d289993, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d289211, d289993, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro74361 q ha hb
  have h18 (q : Pattern) (ha : d289218 q = 1) (hb : d290004 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d289218, d290004, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d289218, d290004, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro74363 q ha hb
  have h19 (q : Pattern) (ha : d289219 q = 1) (hb : d290005 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d289219, d290005, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d289219, d290005, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d289220 q = 1) (hb : d290006 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d289220, d290006, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d289220, d290006, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h21 (q : Pattern) (ha : d289221 q = 1) (hb : d290007 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d289221, d290007, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d289221, d290007, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h22 (q : Pattern) (ha : d289222 q = 1) (hb : d290008 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d289222, d290008, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d289222, d290008, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h23 (q : Pattern) (ha : d289223 q = 1) (hb : d290009 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d289223, d290009, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d289223, d290009, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
  exact h23 p ha hb
theorem andIntro74365 (p : Pattern) (ha : d289229 p = 1) (hb : d290015 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d289224 q = 1) (hb : d290010 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d289224, d290010, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d289224, d290010, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro74364 q ha hb
  have h2 (q : Pattern) (ha : d289225 q = 1) (hb : d290011 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d289225, d290011, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d289225, d290011, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d289226 q = 1) (hb : d290012 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d289226, d290012, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d289226, d290012, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d289227 q = 1) (hb : d290013 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d289227, d290013, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d289227, d290013, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d289228 q = 1) (hb : d290014 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d289228, d290014, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d289228, d290014, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d289229 q = 1) (hb : d290015 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d289229, d290015, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d289229, d290015, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro74366 (p : Pattern) (ha : d289235 p = 1) (hb : d290021 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d288219 q = 1) (hb : d289394 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d288219, d289394, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro74137 q ha hb
    | true =>
      simp only [d288219, d289394, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro74184 q ha hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d288499 q = 1) (hb : d289434 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d288499, d289434, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d288499, d289434, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro74238 q ha hb
  have h3 (q : Pattern) (ha : d288500 q = 1) (hb : d289435 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d288500, d289435, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d288500, d289435, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d288845 q = 1) (hb : d289695 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d288845, d289695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d288845, d289695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro74298 q ha hb
  have h5 (q : Pattern) (ha : d288846 q = 1) (hb : d289696 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d288846, d289696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d288846, d289696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d288847 q = 1) (hb : d289697 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d288847, d289697, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d288847, d289697, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d289230 q = 1) (hb : d290016 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d289230, d290016, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d289230, d290016, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro74365 q ha hb
  have h8 (q : Pattern) (ha : d289231 q = 1) (hb : d290017 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d289231, d290017, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d289231, d290017, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d289232 q = 1) (hb : d290018 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d289232, d290018, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d289232, d290018, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d289233 q = 1) (hb : d290019 q = 1) : d0 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d289233, d290019, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d289233, d290019, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d239076 q = 1) (hb : d280886 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d239076, d280886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d239076, d280886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro71194 q ha hb
  have h12 (q : Pattern) (ha : d239077 q = 1) (hb : d280887 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d239077, d280887, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d239077, d280887, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d239078 q = 1) (hb : d280888 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d239078, d280888, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d239078, d280888, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d239079 q = 1) (hb : d280889 q = 1) : d0 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d239079, d280889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d239079, d280889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d289234 q = 1) (hb : d290020 q = 1) : d0 q = 1 := by
    cases bit : q 10250 with
    | false =>
      simp only [d289234, d290020, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d289234, d290020, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d289235 q = 1) (hb : d290021 q = 1) : d0 q = 1 := by
    cases bit : q 260 with
    | false =>
      simp only [d289235, d290021, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d289235, d290021, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  exact h16 p ha hb
theorem andIntro74367 (p : Pattern) (ha : d289241 p = 1) (hb : d290027 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d289236 q = 1) (hb : d290022 q = 1) : d0 q = 1 := by
    cases bit : q 259 with
    | false =>
      simp only [d289236, d290022, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro74366 q ha hb
    | true =>
      simp only [d289236, d290022, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d289237 q = 1) (hb : d290023 q = 1) : d0 q = 1 := by
    cases bit : q 258 with
    | false =>
      simp only [d289237, d290023, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d289237, d290023, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d289238 q = 1) (hb : d290024 q = 1) : d0 q = 1 := by
    cases bit : q 257 with
    | false =>
      simp only [d289238, d290024, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d289238, d290024, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d289239 q = 1) (hb : d290025 q = 1) : d0 q = 1 := by
    cases bit : q 256 with
    | false =>
      simp only [d289239, d290025, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d289239, d290025, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d289240 q = 1) (hb : d290026 q = 1) : d0 q = 1 := by
    cases bit : q 255 with
    | false =>
      simp only [d289240, d290026, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d289240, d290026, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d289241 q = 1) (hb : d290027 q = 1) : d0 q = 1 := by
    cases bit : q 254 with
    | false =>
      simp only [d289241, d290027, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d289241, d290027, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro74368 (p : Pattern) (ha : d289247 p = 1) (hb : d290033 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d289242 q = 1) (hb : d290028 q = 1) : d0 q = 1 := by
    cases bit : q 253 with
    | false =>
      simp only [d289242, d290028, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro74367 q ha hb
    | true =>
      simp only [d289242, d290028, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d289243 q = 1) (hb : d290029 q = 1) : d0 q = 1 := by
    cases bit : q 252 with
    | false =>
      simp only [d289243, d290029, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d289243, d290029, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d289244 q = 1) (hb : d290030 q = 1) : d0 q = 1 := by
    cases bit : q 251 with
    | false =>
      simp only [d289244, d290030, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d289244, d290030, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d289245 q = 1) (hb : d290031 q = 1) : d0 q = 1 := by
    cases bit : q 250 with
    | false =>
      simp only [d289245, d290031, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d289245, d290031, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d289246 q = 1) (hb : d290032 q = 1) : d0 q = 1 := by
    cases bit : q 249 with
    | false =>
      simp only [d289246, d290032, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d289246, d290032, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d289247 q = 1) (hb : d290033 q = 1) : d0 q = 1 := by
    cases bit : q 245 with
    | false =>
      simp only [d289247, d290033, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d289247, d290033, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro74369 (p : Pattern) (ha : d289253 p = 1) (hb : d290039 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d289248 q = 1) (hb : d290034 q = 1) : d0 q = 1 := by
    cases bit : q 200 with
    | false =>
      simp only [d289248, d290034, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro74368 q ha hb
    | true =>
      simp only [d289248, d290034, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d289249 q = 1) (hb : d290035 q = 1) : d0 q = 1 := by
    cases bit : q 199 with
    | false =>
      simp only [d289249, d290035, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d289249, d290035, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d289250 q = 1) (hb : d290036 q = 1) : d0 q = 1 := by
    cases bit : q 186 with
    | false =>
      simp only [d289250, d290036, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d289250, d290036, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d289251 q = 1) (hb : d290037 q = 1) : d0 q = 1 := by
    cases bit : q 185 with
    | false =>
      simp only [d289251, d290037, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d289251, d290037, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d289252 q = 1) (hb : d290038 q = 1) : d0 q = 1 := by
    cases bit : q 184 with
    | false =>
      simp only [d289252, d290038, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d289252, d290038, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d289253 q = 1) (hb : d290039 q = 1) : d0 q = 1 := by
    cases bit : q 181 with
    | false =>
      simp only [d289253, d290039, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d289253, d290039, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro74370 (p : Pattern) (ha : d289259 p = 1) (hb : d290045 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d289254 q = 1) (hb : d290040 q = 1) : d0 q = 1 := by
    cases bit : q 177 with
    | false =>
      simp only [d289254, d290040, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro74369 q ha hb
    | true =>
      simp only [d289254, d290040, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d289255 q = 1) (hb : d290041 q = 1) : d0 q = 1 := by
    cases bit : q 164 with
    | false =>
      simp only [d289255, d290041, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d289255, d290041, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d289256 q = 1) (hb : d290042 q = 1) : d0 q = 1 := by
    cases bit : q 156 with
    | false =>
      simp only [d289256, d290042, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d289256, d290042, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d289257 q = 1) (hb : d290043 q = 1) : d0 q = 1 := by
    cases bit : q 155 with
    | false =>
      simp only [d289257, d290043, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d289257, d290043, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d289258 q = 1) (hb : d290044 q = 1) : d0 q = 1 := by
    cases bit : q 134 with
    | false =>
      simp only [d289258, d290044, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d289258, d290044, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d289259 q = 1) (hb : d290045 q = 1) : d0 q = 1 := by
    cases bit : q 133 with
    | false =>
      simp only [d289259, d290045, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d289259, d290045, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro74371 (p : Pattern) (ha : d289265 p = 1) (hb : d290051 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d289260 q = 1) (hb : d290046 q = 1) : d0 q = 1 := by
    cases bit : q 120 with
    | false =>
      simp only [d289260, d290046, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro74370 q ha hb
    | true =>
      simp only [d289260, d290046, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d289261 q = 1) (hb : d290047 q = 1) : d0 q = 1 := by
    cases bit : q 118 with
    | false =>
      simp only [d289261, d290047, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d289261, d290047, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d289262 q = 1) (hb : d290048 q = 1) : d0 q = 1 := by
    cases bit : q 114 with
    | false =>
      simp only [d289262, d290048, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d289262, d290048, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d289263 q = 1) (hb : d290049 q = 1) : d0 q = 1 := by
    cases bit : q 111 with
    | false =>
      simp only [d289263, d290049, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d289263, d290049, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d289264 q = 1) (hb : d290050 q = 1) : d0 q = 1 := by
    cases bit : q 98 with
    | false =>
      simp only [d289264, d290050, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d289264, d290050, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d289265 q = 1) (hb : d290051 q = 1) : d0 q = 1 := by
    cases bit : q 97 with
    | false =>
      simp only [d289265, d290051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d289265, d290051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro74372 (p : Pattern) (ha : d289271 p = 1) (hb : d290057 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d289266 q = 1) (hb : d290052 q = 1) : d0 q = 1 := by
    cases bit : q 94 with
    | false =>
      simp only [d289266, d290052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro74371 q ha hb
    | true =>
      simp only [d289266, d290052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d289267 q = 1) (hb : d290053 q = 1) : d0 q = 1 := by
    cases bit : q 76 with
    | false =>
      simp only [d289267, d290053, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d289267, d290053, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d289268 q = 1) (hb : d290054 q = 1) : d0 q = 1 := by
    cases bit : q 67 with
    | false =>
      simp only [d289268, d290054, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d289268, d290054, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d289269 q = 1) (hb : d290055 q = 1) : d0 q = 1 := by
    cases bit : q 52 with
    | false =>
      simp only [d289269, d290055, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d289269, d290055, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d289270 q = 1) (hb : d290056 q = 1) : d0 q = 1 := by
    cases bit : q 47 with
    | false =>
      simp only [d289270, d290056, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d289270, d290056, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d289271 q = 1) (hb : d290057 q = 1) : d0 q = 1 := by
    cases bit : q 46 with
    | false =>
      simp only [d289271, d290057, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d289271, d290057, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro74373 (p : Pattern) (ha : d289277 p = 1) (hb : d290063 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d289272 q = 1) (hb : d290058 q = 1) : d0 q = 1 := by
    cases bit : q 45 with
    | false =>
      simp only [d289272, d290058, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro74372 q ha hb
    | true =>
      simp only [d289272, d290058, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d289273 q = 1) (hb : d290059 q = 1) : d0 q = 1 := by
    cases bit : q 30 with
    | false =>
      simp only [d289273, d290059, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d289273, d290059, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d289274 q = 1) (hb : d290060 q = 1) : d0 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d289274, d290060, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d289274, d290060, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d289275 q = 1) (hb : d290061 q = 1) : d0 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d289275, d290061, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d289275, d290061, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d289276 q = 1) (hb : d290062 q = 1) : d0 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d289276, d290062, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d289276, d290062, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d289277 q = 1) (hb : d290063 q = 1) : d0 q = 1 := by
    cases bit : q 25 with
    | false =>
      simp only [d289277, d290063, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d289277, d290063, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro74374 (p : Pattern) (ha : d53655 p = 1) (hb : d287734 p = 1) : d290066 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d287734 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d49 q = 1) (hb : d287734 q = 1) : d49 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d204 q = 1) (hb : d287734 q = 1) : d40183 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d204, d40183, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73827 q ha hb
    | true =>
      simp only [d204, d40183, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d287 q = 1) (hb : d287734 q = 1) : d40243 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d287, d40243, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d287, d40243, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d288 q = 1) (hb : d287734 q = 1) : d40244 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d288, d40244, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d288, d40244, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d289 q = 1) (hb : d287734 q = 1) : d40245 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d289, d40245, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d289, d40245, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d290 q = 1) (hb : d287734 q = 1) : d40246 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d290, d40246, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d290, d40246, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d53655 q = 1) (hb : d287734 q = 1) : d290066 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d53655, d290066, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53655, d290066, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro74375 (p : Pattern) (ha : d53665 p = 1) (hb : d287734 p = 1) : d290076 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d287734 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d83 q = 1) (hb : d287734 q = 1) : d83 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d244 q = 1) (hb : d287734 q = 1) : d40219 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d244, d40219, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73831 q ha hb
    | true =>
      simp only [d244, d40219, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d53661 q = 1) (hb : d287734 q = 1) : d290072 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d53661, d290072, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53661, d290072, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d53662 q = 1) (hb : d287734 q = 1) : d290073 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d53662, d290073, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d53662, d290073, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d53663 q = 1) (hb : d287734 q = 1) : d290074 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d53663, d290074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53663, d290074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d53664 q = 1) (hb : d287734 q = 1) : d290075 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d53664, d290075, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53664, d290075, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d53665 q = 1) (hb : d287734 q = 1) : d290076 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d53665, d290076, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53665, d290076, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro74376 (p : Pattern) (ha : d53671 p = 1) (hb : d287734 p = 1) : d290082 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d287734 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d292 q = 1) (hb : d287734 q = 1) : d40248 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d292, d40248, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73837 q ha hb
    | true =>
      simp only [d292, d40248, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73838 q ha hb
  have h2 (q : Pattern) (ha : d293 q = 1) (hb : d287734 q = 1) : d40249 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d293, d40249, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d293, d40249, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d53653 q = 1) (hb : d287734 q = 1) : d290064 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d53653, d290064, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d53653, d290064, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d53654 q = 1) (hb : d287734 q = 1) : d290065 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d53654, d290065, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53654, d290065, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d53656 q = 1) (hb : d287734 q = 1) : d290067 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d53656, d290067, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53656, d290067, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro74374 q ha hb
  have h6 (q : Pattern) (ha : d53657 q = 1) (hb : d287734 q = 1) : d290068 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d53657, d290068, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d53657, d290068, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d53658 q = 1) (hb : d287734 q = 1) : d290069 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d53658, d290069, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d53658, d290069, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d53659 q = 1) (hb : d287734 q = 1) : d290070 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d53659, d290070, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d53659, d290070, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d53660 q = 1) (hb : d287734 q = 1) : d290071 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d53660, d290071, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d53660, d290071, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d53666 q = 1) (hb : d287734 q = 1) : d290077 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d53666, d290077, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53666, d290077, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro74375 q ha hb
  have h11 (q : Pattern) (ha : d53667 q = 1) (hb : d287734 q = 1) : d290078 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d53667, d290078, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d53667, d290078, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d53668 q = 1) (hb : d287734 q = 1) : d290079 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d53668, d290079, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d53668, d290079, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d53669 q = 1) (hb : d287734 q = 1) : d290080 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d53669, d290080, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d53669, d290080, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d53670 q = 1) (hb : d287734 q = 1) : d290081 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d53670, d290081, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d53670, d290081, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d53671 q = 1) (hb : d287734 q = 1) : d290082 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d53671, d290082, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d53671, d290082, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro74377 (p : Pattern) (ha : d53677 p = 1) (hb : d287734 p = 1) : d290088 p = 1 := by
  have h0 (q : Pattern) (ha : d53652 q = 1) (hb : d287734 q = 1) : d53652 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d287734 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d53672 q = 1) (hb : d287734 q = 1) : d290083 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d53672, d290083, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d53672, d290083, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro74376 q ha hb
  have h3 (q : Pattern) (ha : d53673 q = 1) (hb : d287734 q = 1) : d290084 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d53673, d290084, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d53673, d290084, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d53674 q = 1) (hb : d287734 q = 1) : d290085 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d53674, d290085, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d53674, d290085, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d53675 q = 1) (hb : d287734 q = 1) : d290086 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d53675, d290086, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d53675, d290086, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d53676 q = 1) (hb : d287734 q = 1) : d290087 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d53676, d290087, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d53676, d290087, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d53677 q = 1) (hb : d287734 q = 1) : d290088 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d53677, d290088, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53677, d290088, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro74378 (p : Pattern) (ha : d171078 p = 1) (hb : d287734 p = 1) : d290091 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d287734 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16052 q = 1) (hb : d287734 q = 1) : d40465 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d16052, d40465, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73874 q ha hb
    | true =>
      simp only [d16052, d40465, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73865 q ha hb
  have h2 (q : Pattern) (ha : d16053 q = 1) (hb : d287734 q = 1) : d40466 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d16053, d40466, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16053, d40466, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d16054 q = 1) (hb : d287734 q = 1) : d40467 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d16054, d40467, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d16054, d40467, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d16055 q = 1) (hb : d287734 q = 1) : d40468 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d16055, d40468, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16055, d40468, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d16056 q = 1) (hb : d287734 q = 1) : d40469 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d16056, d40469, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16056, d40469, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d171078 q = 1) (hb : d287734 q = 1) : d290091 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d171078, d290091, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d171078, d290091, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro74379 (p : Pattern) (ha : d171089 p = 1) (hb : d287734 p = 1) : d290102 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d287734 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d171084 q = 1) (hb : d287734 q = 1) : d290097 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d171084, d290097, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73901 q ha hb
    | true =>
      simp only [d171084, d290097, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73869 q ha hb
  have h2 (q : Pattern) (ha : d171085 q = 1) (hb : d287734 q = 1) : d290098 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d171085, d290098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d171085, d290098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d171086 q = 1) (hb : d287734 q = 1) : d290099 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d171086, d290099, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d171086, d290099, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d171087 q = 1) (hb : d287734 q = 1) : d290100 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d171087, d290100, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d171087, d290100, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d171088 q = 1) (hb : d287734 q = 1) : d290101 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d171088, d290101, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d171088, d290101, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d171089 q = 1) (hb : d287734 q = 1) : d290102 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d171089, d290102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d171089, d290102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro74380 (p : Pattern) (ha : d171095 p = 1) (hb : d287734 p = 1) : d290108 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d287734 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16058 q = 1) (hb : d287734 q = 1) : d40471 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d16058, d40471, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73873 q ha hb
    | true =>
      simp only [d16058, d40471, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73875 q ha hb
  have h2 (q : Pattern) (ha : d16059 q = 1) (hb : d287734 q = 1) : d40472 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d16059, d40472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d16059, d40472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d171076 q = 1) (hb : d287734 q = 1) : d290089 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d171076, d290089, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d171076, d290089, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d171077 q = 1) (hb : d287734 q = 1) : d290090 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d171077, d290090, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d171077, d290090, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d171079 q = 1) (hb : d287734 q = 1) : d290092 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d171079, d290092, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d171079, d290092, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro74378 q ha hb
  have h6 (q : Pattern) (ha : d171080 q = 1) (hb : d287734 q = 1) : d290093 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d171080, d290093, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d171080, d290093, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d171081 q = 1) (hb : d287734 q = 1) : d290094 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d171081, d290094, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d171081, d290094, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d171082 q = 1) (hb : d287734 q = 1) : d290095 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d171082, d290095, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d171082, d290095, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d171083 q = 1) (hb : d287734 q = 1) : d290096 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d171083, d290096, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d171083, d290096, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d171090 q = 1) (hb : d287734 q = 1) : d290103 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d171090, d290103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d171090, d290103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro74379 q ha hb
  have h11 (q : Pattern) (ha : d171091 q = 1) (hb : d287734 q = 1) : d290104 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d171091, d290104, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d171091, d290104, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d171092 q = 1) (hb : d287734 q = 1) : d290105 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d171092, d290105, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d171092, d290105, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d171093 q = 1) (hb : d287734 q = 1) : d290106 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d171093, d290106, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d171093, d290106, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d171094 q = 1) (hb : d287734 q = 1) : d290107 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d171094, d290107, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d171094, d290107, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d171095 q = 1) (hb : d287734 q = 1) : d290108 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d171095, d290108, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d171095, d290108, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro74381 (p : Pattern) (ha : d171101 p = 1) (hb : d287734 p = 1) : d290114 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d287734 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d171096 q = 1) (hb : d287734 q = 1) : d290109 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d171096, d290109, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d171096, d290109, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro74380 q ha hb
  have h2 (q : Pattern) (ha : d171097 q = 1) (hb : d287734 q = 1) : d290110 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d171097, d290110, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d171097, d290110, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d171098 q = 1) (hb : d287734 q = 1) : d290111 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d171098, d290111, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d171098, d290111, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d171099 q = 1) (hb : d287734 q = 1) : d290112 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d171099, d290112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d171099, d290112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d171100 q = 1) (hb : d287734 q = 1) : d290113 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d171100, d290113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d171100, d290113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d171101 q = 1) (hb : d287734 q = 1) : d290114 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d171101, d290114, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d171101, d290114, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro74382 (p : Pattern) (ha : d279792 p = 1) (hb : d287734 p = 1) : d290118 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d287734 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d28858 q = 1) (hb : d287734 q = 1) : d40804 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d28858, d40804, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73927 q ha hb
    | true =>
      simp only [d28858, d40804, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73915 q ha hb
  have h2 (q : Pattern) (ha : d28859 q = 1) (hb : d287734 q = 1) : d40805 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d28859, d40805, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d28859, d40805, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d28860 q = 1) (hb : d287734 q = 1) : d40806 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d28860, d40806, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d28860, d40806, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d28861 q = 1) (hb : d287734 q = 1) : d40807 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d28861, d40807, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d28861, d40807, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d28862 q = 1) (hb : d287734 q = 1) : d40808 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d28862, d40808, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d28862, d40808, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d279792 q = 1) (hb : d287734 q = 1) : d290118 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d279792, d290118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d279792, d290118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro74383 (p : Pattern) (ha : d279803 p = 1) (hb : d287734 p = 1) : d290129 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d287734 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d279798 q = 1) (hb : d287734 q = 1) : d290124 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d279798, d290124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73960 q ha hb
    | true =>
      simp only [d279798, d290124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73921 q ha hb
  have h2 (q : Pattern) (ha : d279799 q = 1) (hb : d287734 q = 1) : d290125 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d279799, d290125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d279799, d290125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d279800 q = 1) (hb : d287734 q = 1) : d290126 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d279800, d290126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d279800, d290126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d279801 q = 1) (hb : d287734 q = 1) : d290127 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d279801, d290127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d279801, d290127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d279802 q = 1) (hb : d287734 q = 1) : d290128 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d279802, d290128, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d279802, d290128, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d279803 q = 1) (hb : d287734 q = 1) : d290129 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d279803, d290129, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d279803, d290129, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro74384 (p : Pattern) (ha : d279809 p = 1) (hb : d287734 p = 1) : d290135 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d287734 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d28864 q = 1) (hb : d287734 q = 1) : d40810 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d28864, d40810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73926 q ha hb
    | true =>
      simp only [d28864, d40810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73928 q ha hb
  have h2 (q : Pattern) (ha : d28865 q = 1) (hb : d287734 q = 1) : d40811 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d28865, d40811, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d28865, d40811, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d279790 q = 1) (hb : d287734 q = 1) : d290116 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d279790, d290116, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d279790, d290116, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d279791 q = 1) (hb : d287734 q = 1) : d290117 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d279791, d290117, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d279791, d290117, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d279793 q = 1) (hb : d287734 q = 1) : d290119 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d279793, d290119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d279793, d290119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro74382 q ha hb
  have h6 (q : Pattern) (ha : d279794 q = 1) (hb : d287734 q = 1) : d290120 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d279794, d290120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d279794, d290120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d279795 q = 1) (hb : d287734 q = 1) : d290121 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d279795, d290121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d279795, d290121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d279796 q = 1) (hb : d287734 q = 1) : d290122 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d279796, d290122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d279796, d290122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d279797 q = 1) (hb : d287734 q = 1) : d290123 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d279797, d290123, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d279797, d290123, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d279804 q = 1) (hb : d287734 q = 1) : d290130 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d279804, d290130, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d279804, d290130, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro74383 q ha hb
  have h11 (q : Pattern) (ha : d279805 q = 1) (hb : d287734 q = 1) : d290131 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d279805, d290131, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d279805, d290131, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d279806 q = 1) (hb : d287734 q = 1) : d290132 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d279806, d290132, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d279806, d290132, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d279807 q = 1) (hb : d287734 q = 1) : d290133 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d279807, d290133, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d279807, d290133, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d279808 q = 1) (hb : d287734 q = 1) : d290134 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d279808, d290134, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d279808, d290134, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d279809 q = 1) (hb : d287734 q = 1) : d290135 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d279809, d290135, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d279809, d290135, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro74385 (p : Pattern) (ha : d279815 p = 1) (hb : d287734 p = 1) : d290141 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d287734 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d279810 q = 1) (hb : d287734 q = 1) : d290136 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d279810, d290136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d279810, d290136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro74384 q ha hb
  have h2 (q : Pattern) (ha : d279811 q = 1) (hb : d287734 q = 1) : d290137 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d279811, d290137, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d279811, d290137, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d279812 q = 1) (hb : d287734 q = 1) : d290138 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d279812, d290138, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d279812, d290138, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d279813 q = 1) (hb : d287734 q = 1) : d290139 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d279813, d290139, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d279813, d290139, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d279814 q = 1) (hb : d287734 q = 1) : d290140 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d279814, d290140, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d279814, d290140, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d279815 q = 1) (hb : d287734 q = 1) : d290141 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d279815, d290141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d279815, d290141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro74386 (p : Pattern) (ha : d279820 p = 1) (hb : d287734 p = 1) : d290146 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d287734 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d29152 q = 1) (hb : d287734 q = 1) : d289489 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d29152, d289489, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73975 q ha hb
    | true =>
      simp only [d29152, d289489, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73976 q ha hb
  have h2 (q : Pattern) (ha : d29153 q = 1) (hb : d287734 q = 1) : d289490 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d29153, d289490, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d29153, d289490, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d29154 q = 1) (hb : d287734 q = 1) : d289491 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d29154, d289491, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d29154, d289491, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d29155 q = 1) (hb : d287734 q = 1) : d289492 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d29155, d289492, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d29155, d289492, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d29156 q = 1) (hb : d287734 q = 1) : d289493 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d29156, d289493, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d29156, d289493, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d279820 q = 1) (hb : d287734 q = 1) : d290146 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d279820, d290146, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d279820, d290146, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro74387 (p : Pattern) (ha : d279831 p = 1) (hb : d287734 p = 1) : d290157 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d287734 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d279826 q = 1) (hb : d287734 q = 1) : d290152 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d279826, d290152, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro74016 q ha hb
    | true =>
      simp only [d279826, d290152, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73984 q ha hb
  have h2 (q : Pattern) (ha : d279827 q = 1) (hb : d287734 q = 1) : d290153 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d279827, d290153, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d279827, d290153, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d279828 q = 1) (hb : d287734 q = 1) : d290154 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d279828, d290154, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d279828, d290154, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d279829 q = 1) (hb : d287734 q = 1) : d290155 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d279829, d290155, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d279829, d290155, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d279830 q = 1) (hb : d287734 q = 1) : d290156 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d279830, d290156, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d279830, d290156, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d279831 q = 1) (hb : d287734 q = 1) : d290157 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d279831, d290157, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d279831, d290157, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro74388 (p : Pattern) (ha : d279837 p = 1) (hb : d287734 p = 1) : d290163 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d287734 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d29158 q = 1) (hb : d287734 q = 1) : d289495 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d29158, d289495, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73974 q ha hb
    | true =>
      simp only [d29158, d289495, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73977 q ha hb
  have h2 (q : Pattern) (ha : d29159 q = 1) (hb : d287734 q = 1) : d289496 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d29159, d289496, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d29159, d289496, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d279818 q = 1) (hb : d287734 q = 1) : d290144 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d279818, d290144, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d279818, d290144, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d279819 q = 1) (hb : d287734 q = 1) : d290145 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d279819, d290145, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d279819, d290145, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d279821 q = 1) (hb : d287734 q = 1) : d290147 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d279821, d290147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d279821, d290147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro74386 q ha hb
  have h6 (q : Pattern) (ha : d279822 q = 1) (hb : d287734 q = 1) : d290148 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d279822, d290148, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d279822, d290148, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d279823 q = 1) (hb : d287734 q = 1) : d290149 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d279823, d290149, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d279823, d290149, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d279824 q = 1) (hb : d287734 q = 1) : d290150 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d279824, d290150, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d279824, d290150, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d279825 q = 1) (hb : d287734 q = 1) : d290151 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d279825, d290151, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d279825, d290151, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d279832 q = 1) (hb : d287734 q = 1) : d290158 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d279832, d290158, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d279832, d290158, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro74387 q ha hb
  have h11 (q : Pattern) (ha : d279833 q = 1) (hb : d287734 q = 1) : d290159 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d279833, d290159, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d279833, d290159, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d279834 q = 1) (hb : d287734 q = 1) : d290160 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d279834, d290160, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d279834, d290160, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d279835 q = 1) (hb : d287734 q = 1) : d290161 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d279835, d290161, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d279835, d290161, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d279836 q = 1) (hb : d287734 q = 1) : d290162 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d279836, d290162, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d279836, d290162, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d279837 q = 1) (hb : d287734 q = 1) : d290163 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d279837, d290163, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d279837, d290163, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro74389 (p : Pattern) (ha : d279843 p = 1) (hb : d287734 p = 1) : d290169 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d287734 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d279838 q = 1) (hb : d287734 q = 1) : d290164 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d279838, d290164, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d279838, d290164, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro74388 q ha hb
  have h2 (q : Pattern) (ha : d279839 q = 1) (hb : d287734 q = 1) : d290165 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d279839, d290165, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d279839, d290165, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d279840 q = 1) (hb : d287734 q = 1) : d290166 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d279840, d290166, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d279840, d290166, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d279841 q = 1) (hb : d287734 q = 1) : d290167 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d279841, d290167, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d279841, d290167, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d279842 q = 1) (hb : d287734 q = 1) : d290168 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d279842, d290168, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d279842, d290168, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d279843 q = 1) (hb : d287734 q = 1) : d290169 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d279843, d290169, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d279843, d290169, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro74390 (p : Pattern) (ha : d279849 p = 1) (hb : d287734 p = 1) : d290175 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d287734 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d29633 q = 1) (hb : d287734 q = 1) : d289773 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d29633, d289773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro74040 q ha hb
    | true =>
      simp only [d29633, d289773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro74041 q ha hb
  have h2 (q : Pattern) (ha : d29634 q = 1) (hb : d287734 q = 1) : d289774 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d29634, d289774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d29634, d289774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d29635 q = 1) (hb : d287734 q = 1) : d289775 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d29635, d289775, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d29635, d289775, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d29636 q = 1) (hb : d287734 q = 1) : d289776 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d29636, d289776, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d29636, d289776, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d29637 q = 1) (hb : d287734 q = 1) : d289777 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d29637, d289777, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d29637, d289777, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d279849 q = 1) (hb : d287734 q = 1) : d290175 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d279849, d290175, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d279849, d290175, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro74391 (p : Pattern) (ha : d279860 p = 1) (hb : d287734 p = 1) : d290186 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d287734 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d279855 q = 1) (hb : d287734 q = 1) : d290181 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d279855, d290181, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro74082 q ha hb
    | true =>
      simp only [d279855, d290181, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro74049 q ha hb
  have h2 (q : Pattern) (ha : d279856 q = 1) (hb : d287734 q = 1) : d290182 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d279856, d290182, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d279856, d290182, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d279857 q = 1) (hb : d287734 q = 1) : d290183 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d279857, d290183, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d279857, d290183, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d279858 q = 1) (hb : d287734 q = 1) : d290184 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d279858, d290184, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d279858, d290184, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d279859 q = 1) (hb : d287734 q = 1) : d290185 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d279859, d290185, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d279859, d290185, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d279860 q = 1) (hb : d287734 q = 1) : d290186 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d279860, d290186, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d279860, d290186, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro74392 (p : Pattern) (ha : d279866 p = 1) (hb : d287734 p = 1) : d290192 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d287734 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d29639 q = 1) (hb : d287734 q = 1) : d289779 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d29639, d289779, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro74039 q ha hb
    | true =>
      simp only [d29639, d289779, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro74042 q ha hb
  have h2 (q : Pattern) (ha : d29640 q = 1) (hb : d287734 q = 1) : d289780 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d29640, d289780, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d29640, d289780, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d279847 q = 1) (hb : d287734 q = 1) : d290173 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d279847, d290173, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d279847, d290173, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d279848 q = 1) (hb : d287734 q = 1) : d290174 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d279848, d290174, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d279848, d290174, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d279850 q = 1) (hb : d287734 q = 1) : d290176 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d279850, d290176, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d279850, d290176, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro74390 q ha hb
  have h6 (q : Pattern) (ha : d279851 q = 1) (hb : d287734 q = 1) : d290177 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d279851, d290177, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d279851, d290177, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d279852 q = 1) (hb : d287734 q = 1) : d290178 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d279852, d290178, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d279852, d290178, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d279853 q = 1) (hb : d287734 q = 1) : d290179 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d279853, d290179, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d279853, d290179, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d279854 q = 1) (hb : d287734 q = 1) : d290180 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d279854, d290180, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d279854, d290180, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d279861 q = 1) (hb : d287734 q = 1) : d290187 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d279861, d290187, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d279861, d290187, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro74391 q ha hb
  have h11 (q : Pattern) (ha : d279862 q = 1) (hb : d287734 q = 1) : d290188 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d279862, d290188, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d279862, d290188, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d279863 q = 1) (hb : d287734 q = 1) : d290189 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d279863, d290189, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d279863, d290189, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d279864 q = 1) (hb : d287734 q = 1) : d290190 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d279864, d290190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d279864, d290190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d279865 q = 1) (hb : d287734 q = 1) : d290191 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d279865, d290191, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d279865, d290191, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d279866 q = 1) (hb : d287734 q = 1) : d290192 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d279866, d290192, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d279866, d290192, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro74393 (p : Pattern) (ha : d279872 p = 1) (hb : d287734 p = 1) : d290198 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d287734 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d279867 q = 1) (hb : d287734 q = 1) : d290193 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d279867, d290193, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d279867, d290193, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro74392 q ha hb
  have h2 (q : Pattern) (ha : d279868 q = 1) (hb : d287734 q = 1) : d290194 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d279868, d290194, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d279868, d290194, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d279869 q = 1) (hb : d287734 q = 1) : d290195 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d279869, d290195, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d279869, d290195, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d279870 q = 1) (hb : d287734 q = 1) : d290196 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d279870, d290196, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d279870, d290196, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d279871 q = 1) (hb : d287734 q = 1) : d290197 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d279871, d290197, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d279871, d290197, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d279872 q = 1) (hb : d287734 q = 1) : d290198 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d279872, d290198, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d279872, d290198, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro74394 (p : Pattern) (ha : d279908 p = 1) (hb : d287734 p = 1) : d290204 p = 1 := by
  have h0 (q : Pattern) (ha : d171102 q = 1) (hb : d287734 q = 1) : d290115 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d171102, d290115, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro74377 q ha hb
    | true =>
      simp only [d171102, d290115, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro74381 q ha hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d287734 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d279816 q = 1) (hb : d287734 q = 1) : d290142 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d279816, d290142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d279816, d290142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro74385 q ha hb
  have h3 (q : Pattern) (ha : d279817 q = 1) (hb : d287734 q = 1) : d290143 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d279817, d290143, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d279817, d290143, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d279844 q = 1) (hb : d287734 q = 1) : d290170 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d279844, d290170, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d279844, d290170, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro74389 q ha hb
  have h5 (q : Pattern) (ha : d279845 q = 1) (hb : d287734 q = 1) : d290171 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d279845, d290171, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d279845, d290171, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d279846 q = 1) (hb : d287734 q = 1) : d290172 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d279846, d290172, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d279846, d290172, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d279873 q = 1) (hb : d287734 q = 1) : d290199 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d279873, d290199, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d279873, d290199, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro74393 q ha hb
  have h8 (q : Pattern) (ha : d279874 q = 1) (hb : d287734 q = 1) : d290200 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d279874, d290200, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d279874, d290200, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d279875 q = 1) (hb : d287734 q = 1) : d290201 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d279875, d290201, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d279875, d290201, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d279876 q = 1) (hb : d287734 q = 1) : d290202 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d279876, d290202, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d279876, d290202, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d279906 q = 1) (hb : d287734 q = 1) : d279906 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d279907 q = 1) (hb : d287734 q = 1) : d290203 q = 1 := by
    cases bit : q 10250 with
    | false =>
      simp only [d279907, d290203, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d279907, d290203, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d279908 q = 1) (hb : d287734 q = 1) : d290204 q = 1 := by
    cases bit : q 260 with
    | false =>
      simp only [d279908, d290204, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d279908, d290204, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  exact h13 p ha hb
theorem andIntro74395 (p : Pattern) (ha : d279914 p = 1) (hb : d287734 p = 1) : d290210 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d287734 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d279909 q = 1) (hb : d287734 q = 1) : d290205 q = 1 := by
    cases bit : q 259 with
    | false =>
      simp only [d279909, d290205, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro74394 q ha hb
    | true =>
      simp only [d279909, d290205, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d279910 q = 1) (hb : d287734 q = 1) : d290206 q = 1 := by
    cases bit : q 258 with
    | false =>
      simp only [d279910, d290206, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d279910, d290206, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d279911 q = 1) (hb : d287734 q = 1) : d290207 q = 1 := by
    cases bit : q 257 with
    | false =>
      simp only [d279911, d290207, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d279911, d290207, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d279912 q = 1) (hb : d287734 q = 1) : d290208 q = 1 := by
    cases bit : q 256 with
    | false =>
      simp only [d279912, d290208, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d279912, d290208, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d279913 q = 1) (hb : d287734 q = 1) : d290209 q = 1 := by
    cases bit : q 255 with
    | false =>
      simp only [d279913, d290209, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d279913, d290209, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d279914 q = 1) (hb : d287734 q = 1) : d290210 q = 1 := by
    cases bit : q 254 with
    | false =>
      simp only [d279914, d290210, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d279914, d290210, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro74396 (p : Pattern) (ha : d279920 p = 1) (hb : d287737 p = 1) : d290216 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d287734 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d279915 q = 1) (hb : d287734 q = 1) : d290211 q = 1 := by
    cases bit : q 253 with
    | false =>
      simp only [d279915, d290211, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro74395 q ha hb
    | true =>
      simp only [d279915, d290211, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d279916 q = 1) (hb : d287734 q = 1) : d290212 q = 1 := by
    cases bit : q 252 with
    | false =>
      simp only [d279916, d290212, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d279916, d290212, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d279917 q = 1) (hb : d287734 q = 1) : d290213 q = 1 := by
    cases bit : q 251 with
    | false =>
      simp only [d279917, d290213, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d279917, d290213, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d279918 q = 1) (hb : d287734 q = 1) : d290214 q = 1 := by
    cases bit : q 250 with
    | false =>
      simp only [d279918, d290214, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d279918, d290214, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d279919 q = 1) (hb : d287734 q = 1) : d290215 q = 1 := by
    cases bit : q 249 with
    | false =>
      simp only [d279919, d290215, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d279919, d290215, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d287736 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d279920 q = 1) (hb : d287737 q = 1) : d290216 q = 1 := by
    cases bit : q 245 with
    | false =>
      simp only [d279920, d287737, d290216, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d279920, d287737, d290216, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro74397 (p : Pattern) (ha : d279926 p = 1) (hb : d287737 p = 1) : d290222 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d287737 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d279921 q = 1) (hb : d287737 q = 1) : d290217 q = 1 := by
    cases bit : q 200 with
    | false =>
      simp only [d279921, d290217, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro74396 q ha hb
    | true =>
      simp only [d279921, d290217, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d279922 q = 1) (hb : d287737 q = 1) : d290218 q = 1 := by
    cases bit : q 199 with
    | false =>
      simp only [d279922, d290218, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d279922, d290218, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d279923 q = 1) (hb : d287737 q = 1) : d290219 q = 1 := by
    cases bit : q 186 with
    | false =>
      simp only [d279923, d290219, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d279923, d290219, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d279924 q = 1) (hb : d287737 q = 1) : d290220 q = 1 := by
    cases bit : q 185 with
    | false =>
      simp only [d279924, d290220, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d279924, d290220, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d279925 q = 1) (hb : d287737 q = 1) : d290221 q = 1 := by
    cases bit : q 184 with
    | false =>
      simp only [d279925, d290221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d279925, d290221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d279926 q = 1) (hb : d287737 q = 1) : d290222 q = 1 := by
    cases bit : q 181 with
    | false =>
      simp only [d279926, d290222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d279926, d290222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro74398 (p : Pattern) (ha : d279932 p = 1) (hb : d287737 p = 1) : d290228 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d287737 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d279927 q = 1) (hb : d287737 q = 1) : d290223 q = 1 := by
    cases bit : q 177 with
    | false =>
      simp only [d279927, d290223, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro74397 q ha hb
    | true =>
      simp only [d279927, d290223, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d279928 q = 1) (hb : d287737 q = 1) : d290224 q = 1 := by
    cases bit : q 164 with
    | false =>
      simp only [d279928, d290224, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d279928, d290224, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d279929 q = 1) (hb : d287737 q = 1) : d290225 q = 1 := by
    cases bit : q 156 with
    | false =>
      simp only [d279929, d290225, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d279929, d290225, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d279930 q = 1) (hb : d287737 q = 1) : d290226 q = 1 := by
    cases bit : q 155 with
    | false =>
      simp only [d279930, d290226, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d279930, d290226, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d279931 q = 1) (hb : d287737 q = 1) : d290227 q = 1 := by
    cases bit : q 134 with
    | false =>
      simp only [d279931, d290227, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d279931, d290227, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d279932 q = 1) (hb : d287737 q = 1) : d290228 q = 1 := by
    cases bit : q 133 with
    | false =>
      simp only [d279932, d290228, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d279932, d290228, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro74399 (p : Pattern) (ha : d279938 p = 1) (hb : d287737 p = 1) : d290234 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d287737 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d279933 q = 1) (hb : d287737 q = 1) : d290229 q = 1 := by
    cases bit : q 120 with
    | false =>
      simp only [d279933, d290229, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro74398 q ha hb
    | true =>
      simp only [d279933, d290229, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d279934 q = 1) (hb : d287737 q = 1) : d290230 q = 1 := by
    cases bit : q 118 with
    | false =>
      simp only [d279934, d290230, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d279934, d290230, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d279935 q = 1) (hb : d287737 q = 1) : d290231 q = 1 := by
    cases bit : q 114 with
    | false =>
      simp only [d279935, d290231, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d279935, d290231, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d279936 q = 1) (hb : d287737 q = 1) : d290232 q = 1 := by
    cases bit : q 111 with
    | false =>
      simp only [d279936, d290232, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d279936, d290232, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d279937 q = 1) (hb : d287737 q = 1) : d290233 q = 1 := by
    cases bit : q 98 with
    | false =>
      simp only [d279937, d290233, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d279937, d290233, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d279938 q = 1) (hb : d287737 q = 1) : d290234 q = 1 := by
    cases bit : q 97 with
    | false =>
      simp only [d279938, d290234, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d279938, d290234, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro74400 (p : Pattern) (ha : d279944 p = 1) (hb : d287737 p = 1) : d290240 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d287737 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d279939 q = 1) (hb : d287737 q = 1) : d290235 q = 1 := by
    cases bit : q 94 with
    | false =>
      simp only [d279939, d290235, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro74399 q ha hb
    | true =>
      simp only [d279939, d290235, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d279940 q = 1) (hb : d287737 q = 1) : d290236 q = 1 := by
    cases bit : q 76 with
    | false =>
      simp only [d279940, d290236, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d279940, d290236, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d279941 q = 1) (hb : d287737 q = 1) : d290237 q = 1 := by
    cases bit : q 67 with
    | false =>
      simp only [d279941, d290237, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d279941, d290237, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d279942 q = 1) (hb : d287737 q = 1) : d290238 q = 1 := by
    cases bit : q 52 with
    | false =>
      simp only [d279942, d290238, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d279942, d290238, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d279943 q = 1) (hb : d287737 q = 1) : d290239 q = 1 := by
    cases bit : q 47 with
    | false =>
      simp only [d279943, d290239, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d279943, d290239, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d279944 q = 1) (hb : d287737 q = 1) : d290240 q = 1 := by
    cases bit : q 46 with
    | false =>
      simp only [d279944, d290240, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d279944, d290240, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro74401 (p : Pattern) (ha : d279950 p = 1) (hb : d287737 p = 1) : d290246 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d287737 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d279945 q = 1) (hb : d287737 q = 1) : d290241 q = 1 := by
    cases bit : q 45 with
    | false =>
      simp only [d279945, d290241, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro74400 q ha hb
    | true =>
      simp only [d279945, d290241, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d279946 q = 1) (hb : d287737 q = 1) : d290242 q = 1 := by
    cases bit : q 30 with
    | false =>
      simp only [d279946, d290242, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d279946, d290242, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d279947 q = 1) (hb : d287737 q = 1) : d290243 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d279947, d290243, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d279947, d290243, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d279948 q = 1) (hb : d287737 q = 1) : d290244 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d279948, d290244, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d279948, d290244, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d279949 q = 1) (hb : d287737 q = 1) : d290245 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d279949, d290245, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d279949, d290245, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d279950 q = 1) (hb : d287737 q = 1) : d290246 q = 1 := by
    cases bit : q 25 with
    | false =>
      simp only [d279950, d290246, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d279950, d290246, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro74402 (p : Pattern) (ha : d104 p = 1) (hb : d287770 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d51972 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d51978 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d287765 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d43 q = 1) (hb : d51895 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d43, d51895, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5 q ha hb
    | true =>
      simp only [d43, d51895, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d100 q = 1) (hb : d287766 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d100, d287766, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d100, d287766, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d51896 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d101 q = 1) (hb : d287767 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d101, d287767, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d101, d287767, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d102 q = 1) (hb : d287768 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d102, d287768, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d102, d287768, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d103 q = 1) (hb : d287769 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d103, d287769, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d103, d287769, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d104 q = 1) (hb : d287770 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d104, d287770, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d104, d287770, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro74403 (p : Pattern) (ha : d111 p = 1) (hb : d287777 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d51972 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d51978 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d287765 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d43 q = 1) (hb : d51895 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d43, d51895, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5 q ha hb
    | true =>
      simp only [d43, d51895, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d100 q = 1) (hb : d287766 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d100, d287766, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d100, d287766, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d51896 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d101 q = 1) (hb : d287767 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d101, d287767, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d101, d287767, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d102 q = 1) (hb : d287768 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d102, d287768, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d102, d287768, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d103 q = 1) (hb : d287769 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d103, d287769, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d103, d287769, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d52018 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d52022 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d287772 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d50 q = 1) (hb : d51902 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d50, d51902, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7 q ha hb
    | true =>
      simp only [d50, d51902, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h14 (q : Pattern) (ha : d107 q = 1) (hb : d287773 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d107, d287773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d107, d287773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d0 q = 1) (hb : d51903 q = 1) : d0 q = 1 := by
    exact ha
  have h16 (q : Pattern) (ha : d108 q = 1) (hb : d287774 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d108, d287774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d108, d287774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d109 q = 1) (hb : d287775 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d109, d287775, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d109, d287775, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d110 q = 1) (hb : d287776 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d110, d287776, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d110, d287776, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d111 q = 1) (hb : d287777 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d111, d287777, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d111, d287777, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro74404 (p : Pattern) (ha : d406 p = 1) (hb : d287784 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d287772 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d50 q = 1) (hb : d51902 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d50, d51902, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7 q ha hb
    | true =>
      simp only [d50, d51902, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d107 q = 1) (hb : d287773 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d107, d287773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d107, d287773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d51903 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d108 q = 1) (hb : d287774 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d108, d287774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d108, d287774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d109 q = 1) (hb : d287782 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d109, d287782, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d109, d287782, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d110 q = 1) (hb : d287783 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d110, d287783, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d110, d287783, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d406 q = 1) (hb : d287784 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d406, d287784, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d406, d287784, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro74405 (p : Pattern) (ha : d462 p = 1) (hb : d287813 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d287808 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d84 q = 1) (hb : d51936 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d84, d51936, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12 q ha hb
    | true =>
      simp only [d84, d51936, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d458 q = 1) (hb : d287809 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d458, d287809, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d458, d287809, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d51937 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d459 q = 1) (hb : d287810 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d459, d287810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d459, d287810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d460 q = 1) (hb : d287811 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d460, d287811, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d460, d287811, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d461 q = 1) (hb : d287812 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d461, d287812, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d461, d287812, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d462 q = 1) (hb : d287813 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d462, d287813, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d462, d287813, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro74406 (p : Pattern) (ha : d53647 p = 1) (hb : d287819 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d51966 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d112 q = 1) (hb : d287778 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d112, d287778, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro74402 q ha hb
    | true =>
      simp only [d112, d287778, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro74403 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d52032 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d113 q = 1) (hb : d287779 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d113, d287779, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d113, d287779, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d53637 q = 1) (hb : d287780 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d53637, d287780, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d53637, d287780, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d53638 q = 1) (hb : d287781 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d53638, d287781, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53638, d287781, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d407 q = 1) (hb : d287785 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d407, d287785, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d407, d287785, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro74404 q ha hb
  have h8 (q : Pattern) (ha : d53639 q = 1) (hb : d287786 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d53639, d287786, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d53639, d287786, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h9 (q : Pattern) (ha : d53640 q = 1) (hb : d287787 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d53640, d287787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d53640, d287787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h10 (q : Pattern) (ha : d53641 q = 1) (hb : d287788 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d53641, d287788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d53641, d287788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h11 (q : Pattern) (ha : d53642 q = 1) (hb : d287789 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d53642, d287789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d53642, d287789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d463 q = 1) (hb : d287814 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d463, d287814, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d463, d287814, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro74405 q ha hb
  have h13 (q : Pattern) (ha : d53643 q = 1) (hb : d287815 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d53643, d287815, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d53643, d287815, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h14 (q : Pattern) (ha : d53644 q = 1) (hb : d287816 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d53644, d287816, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d53644, d287816, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h15 (q : Pattern) (ha : d53645 q = 1) (hb : d287817 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d53645, d287817, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d53645, d287817, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h16 (q : Pattern) (ha : d53646 q = 1) (hb : d287818 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d53646, d287818, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d53646, d287818, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h17 (q : Pattern) (ha : d53647 q = 1) (hb : d287819 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d53647, d287819, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d53647, d287819, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  exact h17 p ha hb
theorem andIntro74407 (p : Pattern) (ha : d40240 p = 1) (hb : d287897 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d287845 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d287851 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d287886 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d40176 q = 1) (hb : d287765 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d40176, d287765, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro74102 q ha hb
    | true =>
      simp only [d40176, d287765, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5 q ha hb
  have h5 (q : Pattern) (ha : d40236 q = 1) (hb : d287887 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d40236, d287887, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d40236, d287887, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d287893 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d40237 q = 1) (hb : d287894 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d40237, d287894, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d40237, d287894, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d40238 q = 1) (hb : d287895 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d40238, d287895, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d40238, d287895, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d40239 q = 1) (hb : d287896 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d40239, d287896, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d40239, d287896, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d40240 q = 1) (hb : d287897 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d40240, d287897, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d40240, d287897, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro74408 (p : Pattern) (ha : d40247 p = 1) (hb : d287916 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d287845 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d287851 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d287886 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d40176 q = 1) (hb : d287765 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d40176, d287765, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro74102 q ha hb
    | true =>
      simp only [d40176, d287765, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5 q ha hb
  have h4 (q : Pattern) (ha : d40236 q = 1) (hb : d287887 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d40236, d287887, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d40236, d287887, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d287893 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d40237 q = 1) (hb : d287894 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d40237, d287894, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d40237, d287894, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d40238 q = 1) (hb : d287895 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d40238, d287895, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d40238, d287895, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d40239 q = 1) (hb : d287896 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d40239, d287896, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d40239, d287896, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d287902 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d287906 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d287908 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d40183 q = 1) (hb : d287772 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d40183, d287772, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro74104 q ha hb
    | true =>
      simp only [d40183, d287772, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7 q ha hb
  have h13 (q : Pattern) (ha : d40243 q = 1) (hb : d287909 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d40243, d287909, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d40243, d287909, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d287912 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d40244 q = 1) (hb : d287913 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d40244, d287913, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d40244, d287913, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d40245 q = 1) (hb : d287914 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d40245, d287914, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d40245, d287914, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d40246 q = 1) (hb : d287915 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d40246, d287915, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d40246, d287915, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d40247 q = 1) (hb : d287916 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d40247, d287916, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d40247, d287916, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro74409 (p : Pattern) (ha : d287925 p = 1) (hb : d290066 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d287908 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d40183 q = 1) (hb : d287772 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d40183, d287772, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro74104 q ha hb
    | true =>
      simp only [d40183, d287772, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7 q ha hb
  have h3 (q : Pattern) (ha : d40243 q = 1) (hb : d287909 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d40243, d287909, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d40243, d287909, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d287912 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d40244 q = 1) (hb : d287913 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d40244, d287913, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d40244, d287913, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d40245 q = 1) (hb : d287923 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d40245, d287923, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d40245, d287923, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d40246 q = 1) (hb : d287924 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d40246, d287924, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d40246, d287924, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d287925 q = 1) (hb : d290066 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d287925, d290066, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d287925, d290066, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
  exact h8 p ha hb
theorem andIntro74410 (p : Pattern) (ha : d287965 p = 1) (hb : d290076 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d287954 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d40219 q = 1) (hb : d287808 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d40219, d287808, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro74109 q ha hb
    | true =>
      simp only [d40219, d287808, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12 q ha hb
  have h3 (q : Pattern) (ha : d287955 q = 1) (hb : d290072 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d287955, d290072, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d287955, d290072, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d287961 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d287962 q = 1) (hb : d290073 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d287962, d290073, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d287962, d290073, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d287963 q = 1) (hb : d290074 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d287963, d290074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d287963, d290074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d287964 q = 1) (hb : d290075 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d287964, d290075, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d287964, d290075, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d287965 q = 1) (hb : d290076 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d287965, d290076, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d287965, d290076, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro74411 (p : Pattern) (ha : d287971 p = 1) (hb : d290082 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d287839 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d40248 q = 1) (hb : d287917 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d40248, d287917, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro74407 q ha hb
    | true =>
      simp only [d40248, d287917, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro74408 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d287919 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d40249 q = 1) (hb : d287920 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d40249, d287920, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d40249, d287920, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d287921 q = 1) (hb : d290064 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d287921, d290064, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d287921, d290064, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d287922 q = 1) (hb : d290065 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d287922, d290065, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d287922, d290065, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d287926 q = 1) (hb : d290067 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d287926, d290067, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d287926, d290067, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro74409 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d52173 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d287927 q = 1) (hb : d290068 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d287927, d290068, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d287927, d290068, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d287928 q = 1) (hb : d290069 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d287928, d290069, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d287928, d290069, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h11 (q : Pattern) (ha : d287929 q = 1) (hb : d290070 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d287929, d290070, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d287929, d290070, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h12 (q : Pattern) (ha : d287930 q = 1) (hb : d290071 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d287930, d290071, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d287930, d290071, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d287966 q = 1) (hb : d290077 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d287966, d290077, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d287966, d290077, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro74410 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d52210 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d287967 q = 1) (hb : d290078 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d287967, d290078, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d287967, d290078, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d287968 q = 1) (hb : d290079 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d287968, d290079, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d287968, d290079, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h17 (q : Pattern) (ha : d287969 q = 1) (hb : d290080 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d287969, d290080, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d287969, d290080, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h18 (q : Pattern) (ha : d287970 q = 1) (hb : d290081 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d287970, d290081, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d287970, d290081, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h19 (q : Pattern) (ha : d287971 q = 1) (hb : d290082 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d287971, d290082, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d287971, d290082, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro74412 (p : Pattern) (ha : d287977 p = 1) (hb : d290088 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d51951 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d53648 q = 1) (hb : d287820 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d53648, d287820, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d53648, d287820, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro74406 q ha hb
  have h3 (q : Pattern) (ha : d53649 q = 1) (hb : d287821 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d53649, d287821, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d53649, d287821, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d53650 q = 1) (hb : d287822 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d53650, d287822, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d53650, d287822, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d53651 q = 1) (hb : d287823 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d53651, d287823, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d53651, d287823, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d53652 q = 1) (hb : d287824 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d53652, d287824, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53652, d287824, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d287972 q = 1) (hb : d290083 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d287972, d290083, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d287972, d290083, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro74411 q ha hb
  have h8 (q : Pattern) (ha : d287973 q = 1) (hb : d290084 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d287973, d290084, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d287973, d290084, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d287974 q = 1) (hb : d290085 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d287974, d290085, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d287974, d290085, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d287975 q = 1) (hb : d290086 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d287975, d290086, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d287975, d290086, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d287976 q = 1) (hb : d290087 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d287976, d290087, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d287976, d290087, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d287977 q = 1) (hb : d290088 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d287977, d290088, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
    | true =>
      simp only [d287977, d290088, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  exact h12 p ha hb
theorem andIntro74413 (p : Pattern) (ha : d40460 p = 1) (hb : d288090 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d288021 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d288030 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d288079 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d40455 q = 1) (hb : d287995 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d40455, d287995, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro74140 q ha hb
    | true =>
      simp only [d40455, d287995, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro74141 q ha hb
  have h5 (q : Pattern) (ha : d40456 q = 1) (hb : d288080 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d40456, d288080, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d40456, d288080, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d288086 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d40457 q = 1) (hb : d288087 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d40457, d288087, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d40457, d288087, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d40458 q = 1) (hb : d288088 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d40458, d288088, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d40458, d288088, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d40459 q = 1) (hb : d288089 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d40459, d288089, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d40459, d288089, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d40460 q = 1) (hb : d288090 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d40460, d288090, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d40460, d288090, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro74414 (p : Pattern) (ha : d40470 p = 1) (hb : d288111 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d288021 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d288030 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d288079 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d40455 q = 1) (hb : d287995 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d40455, d287995, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro74140 q ha hb
    | true =>
      simp only [d40455, d287995, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro74141 q ha hb
  have h4 (q : Pattern) (ha : d40456 q = 1) (hb : d288080 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d40456, d288080, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d40456, d288080, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d288086 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d40457 q = 1) (hb : d288087 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d40457, d288087, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d40457, d288087, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d40458 q = 1) (hb : d288088 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d40458, d288088, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d40458, d288088, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d40459 q = 1) (hb : d288089 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d40459, d288089, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d40459, d288089, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d288096 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d288101 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d288103 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d40465 q = 1) (hb : d288005 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d40465, d288005, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro74143 q ha hb
    | true =>
      simp only [d40465, d288005, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro74144 q ha hb
  have h13 (q : Pattern) (ha : d40466 q = 1) (hb : d288104 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d40466, d288104, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d40466, d288104, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d288107 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d40467 q = 1) (hb : d288108 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d40467, d288108, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d40467, d288108, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d40468 q = 1) (hb : d288109 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d40468, d288109, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d40468, d288109, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d40469 q = 1) (hb : d288110 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d40469, d288110, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d40469, d288110, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d40470 q = 1) (hb : d288111 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d40470, d288111, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d40470, d288111, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro74415 (p : Pattern) (ha : d288131 p = 1) (hb : d290091 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d288103 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d40465 q = 1) (hb : d288005 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d40465, d288005, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro74143 q ha hb
    | true =>
      simp only [d40465, d288005, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro74144 q ha hb
  have h3 (q : Pattern) (ha : d40466 q = 1) (hb : d288104 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d40466, d288104, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d40466, d288104, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d288107 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d40467 q = 1) (hb : d288108 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d40467, d288108, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d40467, d288108, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d40468 q = 1) (hb : d288129 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d40468, d288129, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d40468, d288129, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d40469 q = 1) (hb : d288130 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d40469, d288130, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d40469, d288130, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d288131 q = 1) (hb : d290091 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d288131, d290091, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d288131, d290091, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
  exact h8 p ha hb
theorem andIntro74416 (p : Pattern) (ha : d288199 p = 1) (hb : d290102 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d288183 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d288188 q = 1) (hb : d290097 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d288188, d290097, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro74180 q hb ha
    | true =>
      simp only [d288188, d290097, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro74150 q hb ha
  have h3 (q : Pattern) (ha : d288189 q = 1) (hb : d290098 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d288189, d290098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d288189, d290098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d288195 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d288196 q = 1) (hb : d290099 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d288196, d290099, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d288196, d290099, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d288197 q = 1) (hb : d290100 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d288197, d290100, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d288197, d290100, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d288198 q = 1) (hb : d290101 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d288198, d290101, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d288198, d290101, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d288199 q = 1) (hb : d290102 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d288199, d290102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d288199, d290102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro74417 (p : Pattern) (ha : d288212 p = 1) (hb : d290108 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d288013 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d40471 q = 1) (hb : d288112 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d40471, d288112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro74413 q ha hb
    | true =>
      simp only [d40471, d288112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro74414 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d288125 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d40472 q = 1) (hb : d288126 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d40472, d288126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d40472, d288126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d288127 q = 1) (hb : d290089 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d288127, d290089, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d288127, d290089, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d288128 q = 1) (hb : d290090 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d288128, d290090, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d288128, d290090, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d288132 q = 1) (hb : d290092 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d288132, d290092, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d288132, d290092, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro74415 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d288134 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d288135 q = 1) (hb : d290093 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d288135, d290093, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d288135, d290093, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d288136 q = 1) (hb : d290094 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d288136, d290094, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d288136, d290094, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h11 (q : Pattern) (ha : d288137 q = 1) (hb : d290095 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d288137, d290095, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d288137, d290095, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h12 (q : Pattern) (ha : d288138 q = 1) (hb : d290096 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d288138, d290096, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d288138, d290096, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d288200 q = 1) (hb : d290103 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d288200, d290103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d288200, d290103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro74416 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d288207 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d288208 q = 1) (hb : d290104 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d288208, d290104, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d288208, d290104, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d288209 q = 1) (hb : d290105 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d288209, d290105, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d288209, d290105, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h17 (q : Pattern) (ha : d288210 q = 1) (hb : d290106 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d288210, d290106, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d288210, d290106, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h18 (q : Pattern) (ha : d288211 q = 1) (hb : d290107 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d288211, d290107, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d288211, d290107, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h19 (q : Pattern) (ha : d288212 q = 1) (hb : d290108 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d288212, d290108, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d288212, d290108, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro74418 (p : Pattern) (ha : d288218 p = 1) (hb : d290114 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d288213 q = 1) (hb : d290109 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d288213, d290109, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d288213, d290109, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro74417 q ha hb
  have h2 (q : Pattern) (ha : d288214 q = 1) (hb : d290110 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d288214, d290110, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d288214, d290110, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d288215 q = 1) (hb : d290111 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d288215, d290111, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d288215, d290111, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d288216 q = 1) (hb : d290112 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d288216, d290112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d288216, d290112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d288217 q = 1) (hb : d290113 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d288217, d290113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d288217, d290113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d288218 q = 1) (hb : d290114 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d288218, d290114, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d288218, d290114, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro74419 (p : Pattern) (ha : d40799 p = 1) (hb : d288353 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d288281 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d288290 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d288342 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d40794 q = 1) (hb : d288255 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d40794, d288255, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro74191 q ha hb
    | true =>
      simp only [d40794, d288255, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro74192 q ha hb
  have h5 (q : Pattern) (ha : d40795 q = 1) (hb : d288343 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d40795, d288343, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d40795, d288343, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d288349 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d40796 q = 1) (hb : d288350 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d40796, d288350, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d40796, d288350, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d40797 q = 1) (hb : d288351 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d40797, d288351, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d40797, d288351, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d40798 q = 1) (hb : d288352 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d40798, d288352, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d40798, d288352, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d40799 q = 1) (hb : d288353 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d40799, d288353, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d40799, d288353, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro74420 (p : Pattern) (ha : d40809 p = 1) (hb : d288374 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d288281 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d288290 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d288342 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d40794 q = 1) (hb : d288255 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d40794, d288255, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro74191 q ha hb
    | true =>
      simp only [d40794, d288255, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro74192 q ha hb
  have h4 (q : Pattern) (ha : d40795 q = 1) (hb : d288343 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d40795, d288343, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d40795, d288343, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d288349 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d40796 q = 1) (hb : d288350 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d40796, d288350, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d40796, d288350, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d40797 q = 1) (hb : d288351 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d40797, d288351, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d40797, d288351, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d40798 q = 1) (hb : d288352 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d40798, d288352, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d40798, d288352, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d288359 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d288364 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d288366 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d40804 q = 1) (hb : d288265 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d40804, d288265, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro74194 q ha hb
    | true =>
      simp only [d40804, d288265, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro74195 q ha hb
  have h13 (q : Pattern) (ha : d40805 q = 1) (hb : d288367 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d40805, d288367, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d40805, d288367, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d288370 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d40806 q = 1) (hb : d288371 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d40806, d288371, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d40806, d288371, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d40807 q = 1) (hb : d288372 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d40807, d288372, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d40807, d288372, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d40808 q = 1) (hb : d288373 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d40808, d288373, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d40808, d288373, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d40809 q = 1) (hb : d288374 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d40809, d288374, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d40809, d288374, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro74421 (p : Pattern) (ha : d288394 p = 1) (hb : d290118 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d288366 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d40804 q = 1) (hb : d288265 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d40804, d288265, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro74194 q ha hb
    | true =>
      simp only [d40804, d288265, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro74195 q ha hb
  have h3 (q : Pattern) (ha : d40805 q = 1) (hb : d288367 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d40805, d288367, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d40805, d288367, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d288370 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d40806 q = 1) (hb : d288371 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d40806, d288371, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d40806, d288371, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d40807 q = 1) (hb : d288392 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d40807, d288392, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d40807, d288392, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d40808 q = 1) (hb : d288393 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d40808, d288393, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d40808, d288393, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d288394 q = 1) (hb : d290118 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d288394, d290118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d288394, d290118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
  exact h8 p ha hb
theorem andIntro74422 (p : Pattern) (ha : d288479 p = 1) (hb : d290129 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d288463 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d288468 q = 1) (hb : d290124 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d288468, d290124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro74234 q hb ha
    | true =>
      simp only [d288468, d290124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro74203 q hb ha
  have h3 (q : Pattern) (ha : d288469 q = 1) (hb : d290125 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d288469, d290125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d288469, d290125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d288475 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d288476 q = 1) (hb : d290126 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d288476, d290126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d288476, d290126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d288477 q = 1) (hb : d290127 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d288477, d290127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d288477, d290127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d288478 q = 1) (hb : d290128 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d288478, d290128, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d288478, d290128, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d288479 q = 1) (hb : d290129 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d288479, d290129, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d288479, d290129, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro74423 (p : Pattern) (ha : d288492 p = 1) (hb : d290135 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d288273 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d40810 q = 1) (hb : d288375 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d40810, d288375, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro74419 q ha hb
    | true =>
      simp only [d40810, d288375, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro74420 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d288388 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d40811 q = 1) (hb : d288389 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d40811, d288389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d40811, d288389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d288390 q = 1) (hb : d290116 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d288390, d290116, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d288390, d290116, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d288391 q = 1) (hb : d290117 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d288391, d290117, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d288391, d290117, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d288395 q = 1) (hb : d290119 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d288395, d290119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d288395, d290119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro74421 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d288397 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d288398 q = 1) (hb : d290120 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d288398, d290120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d288398, d290120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d288399 q = 1) (hb : d290121 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d288399, d290121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d288399, d290121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h11 (q : Pattern) (ha : d288400 q = 1) (hb : d290122 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d288400, d290122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d288400, d290122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h12 (q : Pattern) (ha : d288401 q = 1) (hb : d290123 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d288401, d290123, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d288401, d290123, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d288480 q = 1) (hb : d290130 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d288480, d290130, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d288480, d290130, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro74422 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d288487 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d288488 q = 1) (hb : d290131 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d288488, d290131, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d288488, d290131, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d288489 q = 1) (hb : d290132 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d288489, d290132, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d288489, d290132, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h17 (q : Pattern) (ha : d288490 q = 1) (hb : d290133 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d288490, d290133, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d288490, d290133, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h18 (q : Pattern) (ha : d288491 q = 1) (hb : d290134 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d288491, d290134, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d288491, d290134, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h19 (q : Pattern) (ha : d288492 q = 1) (hb : d290135 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d288492, d290135, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d288492, d290135, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro74424 (p : Pattern) (ha : d288498 p = 1) (hb : d290141 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d288493 q = 1) (hb : d290136 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d288493, d290136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d288493, d290136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro74423 q ha hb
  have h2 (q : Pattern) (ha : d288494 q = 1) (hb : d290137 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d288494, d290137, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d288494, d290137, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d288495 q = 1) (hb : d290138 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d288495, d290138, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d288495, d290138, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d288496 q = 1) (hb : d290139 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d288496, d290139, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d288496, d290139, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d288497 q = 1) (hb : d290140 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d288497, d290140, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d288497, d290140, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d288498 q = 1) (hb : d290141 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d288498, d290141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d288498, d290141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro74425 (p : Pattern) (ha : d288672 p = 1) (hb : d289484 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d288600 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d288609 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d288652 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d288574 q = 1) (hb : d289479 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d288574, d289479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro74249 q ha hb
    | true =>
      simp only [d288574, d289479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro74250 q ha hb
  have h5 (q : Pattern) (ha : d288653 q = 1) (hb : d289480 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d288653, d289480, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d288653, d289480, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d288668 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d288669 q = 1) (hb : d289481 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d288669, d289481, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d288669, d289481, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d288670 q = 1) (hb : d289482 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d288670, d289482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d288670, d289482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d288671 q = 1) (hb : d289483 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d288671, d289483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d288671, d289483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d288672 q = 1) (hb : d289484 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d288672, d289484, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d288672, d289484, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro74426 (p : Pattern) (ha : d288693 p = 1) (hb : d289494 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d288600 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d288609 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d288652 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d288574 q = 1) (hb : d289479 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d288574, d289479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro74249 q ha hb
    | true =>
      simp only [d288574, d289479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro74250 q ha hb
  have h4 (q : Pattern) (ha : d288653 q = 1) (hb : d289480 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d288653, d289480, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d288653, d289480, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d288668 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d288669 q = 1) (hb : d289481 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d288669, d289481, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d288669, d289481, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d288670 q = 1) (hb : d289482 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d288670, d289482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d288670, d289482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d288671 q = 1) (hb : d289483 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d288671, d289483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d288671, d289483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d288678 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d288683 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d288685 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d288584 q = 1) (hb : d289489 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d288584, d289489, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro74252 q ha hb
    | true =>
      simp only [d288584, d289489, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro74253 q ha hb
  have h13 (q : Pattern) (ha : d288686 q = 1) (hb : d289490 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d288686, d289490, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
    | true =>
      simp only [d288686, d289490, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d288689 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d288690 q = 1) (hb : d289491 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d288690, d289491, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d288690, d289491, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d288691 q = 1) (hb : d289492 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d288691, d289492, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
    | true =>
      simp only [d288691, d289492, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d288692 q = 1) (hb : d289493 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d288692, d289493, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
    | true =>
      simp only [d288692, d289493, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d288693 q = 1) (hb : d289494 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d288693, d289494, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d288693, d289494, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro74427 (p : Pattern) (ha : d288713 p = 1) (hb : d290146 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d288685 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d288584 q = 1) (hb : d289489 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d288584, d289489, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro74252 q ha hb
    | true =>
      simp only [d288584, d289489, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro74253 q ha hb
  have h3 (q : Pattern) (ha : d288686 q = 1) (hb : d289490 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d288686, d289490, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d288686, d289490, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d288689 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d288690 q = 1) (hb : d289491 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d288690, d289491, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d288690, d289491, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d288711 q = 1) (hb : d289492 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d288711, d289492, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d288711, d289492, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d288712 q = 1) (hb : d289493 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d288712, d289493, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d288712, d289493, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d288713 q = 1) (hb : d290146 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d288713, d290146, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d288713, d290146, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro74428 (p : Pattern) (ha : d288825 p = 1) (hb : d290157 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d288800 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d288805 q = 1) (hb : d290152 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d288805, d290152, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro74290 q ha hb
    | true =>
      simp only [d288805, d290152, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro74295 q ha hb
  have h3 (q : Pattern) (ha : d288806 q = 1) (hb : d290153 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d288806, d290153, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d288806, d290153, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d288821 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d288822 q = 1) (hb : d290154 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d288822, d290154, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d288822, d290154, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d288823 q = 1) (hb : d290155 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d288823, d290155, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d288823, d290155, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d288824 q = 1) (hb : d290156 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d288824, d290156, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d288824, d290156, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d288825 q = 1) (hb : d290157 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d288825, d290157, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d288825, d290157, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro74429 (p : Pattern) (ha : d288838 p = 1) (hb : d290163 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d288592 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d288694 q = 1) (hb : d289495 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d288694, d289495, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro74425 q ha hb
    | true =>
      simp only [d288694, d289495, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro74426 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d288707 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d288708 q = 1) (hb : d289496 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d288708, d289496, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d288708, d289496, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d288709 q = 1) (hb : d290144 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d288709, d290144, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d288709, d290144, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d288710 q = 1) (hb : d290145 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d288710, d290145, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d288710, d290145, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d288714 q = 1) (hb : d290147 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d288714, d290147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d288714, d290147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro74427 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d288716 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d288717 q = 1) (hb : d290148 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d288717, d290148, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d288717, d290148, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d288718 q = 1) (hb : d290149 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d288718, d290149, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d288718, d290149, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h11 (q : Pattern) (ha : d288719 q = 1) (hb : d290150 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d288719, d290150, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d288719, d290150, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h12 (q : Pattern) (ha : d288720 q = 1) (hb : d290151 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d288720, d290151, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d288720, d290151, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d288826 q = 1) (hb : d290158 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d288826, d290158, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d288826, d290158, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro74428 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d288833 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d288834 q = 1) (hb : d290159 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d288834, d290159, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d288834, d290159, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d288835 q = 1) (hb : d290160 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d288835, d290160, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d288835, d290160, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h17 (q : Pattern) (ha : d288836 q = 1) (hb : d290161 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d288836, d290161, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d288836, d290161, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h18 (q : Pattern) (ha : d288837 q = 1) (hb : d290162 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d288837, d290162, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d288837, d290162, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h19 (q : Pattern) (ha : d288838 q = 1) (hb : d290163 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d288838, d290163, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d288838, d290163, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro74430 (p : Pattern) (ha : d288844 p = 1) (hb : d290169 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d288839 q = 1) (hb : d290164 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d288839, d290164, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d288839, d290164, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro74429 q ha hb
  have h2 (q : Pattern) (ha : d288840 q = 1) (hb : d290165 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d288840, d290165, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d288840, d290165, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d288841 q = 1) (hb : d290166 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d288841, d290166, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d288841, d290166, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d288842 q = 1) (hb : d290167 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d288842, d290167, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d288842, d290167, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d288843 q = 1) (hb : d290168 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d288843, d290168, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d288843, d290168, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d288844 q = 1) (hb : d290169 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d288844, d290169, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d288844, d290169, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro74431 (p : Pattern) (ha : d289046 p = 1) (hb : d289768 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d288974 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d288983 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d289013 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d288948 q = 1) (hb : d289763 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d288948, d289763, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro74313 q ha hb
    | true =>
      simp only [d288948, d289763, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro74314 q ha hb
  have h5 (q : Pattern) (ha : d289014 q = 1) (hb : d289764 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d289014, d289764, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d289014, d289764, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d289042 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d289043 q = 1) (hb : d289765 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d289043, d289765, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d289043, d289765, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d289044 q = 1) (hb : d289766 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d289044, d289766, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d289044, d289766, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d289045 q = 1) (hb : d289767 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d289045, d289767, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d289045, d289767, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d289046 q = 1) (hb : d289768 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d289046, d289768, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d289046, d289768, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro74432 (p : Pattern) (ha : d289067 p = 1) (hb : d289778 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d288974 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d288983 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d289013 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d288948 q = 1) (hb : d289763 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d288948, d289763, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro74313 q ha hb
    | true =>
      simp only [d288948, d289763, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro74314 q ha hb
  have h4 (q : Pattern) (ha : d289014 q = 1) (hb : d289764 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d289014, d289764, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d289014, d289764, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d289042 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d289043 q = 1) (hb : d289765 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d289043, d289765, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d289043, d289765, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d289044 q = 1) (hb : d289766 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d289044, d289766, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d289044, d289766, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d289045 q = 1) (hb : d289767 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d289045, d289767, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d289045, d289767, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d289052 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d289057 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d289059 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d288958 q = 1) (hb : d289773 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d288958, d289773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro74316 q ha hb
    | true =>
      simp only [d288958, d289773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro74317 q ha hb
  have h13 (q : Pattern) (ha : d289060 q = 1) (hb : d289774 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d289060, d289774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
    | true =>
      simp only [d289060, d289774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d289063 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d289064 q = 1) (hb : d289775 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d289064, d289775, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d289064, d289775, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d289065 q = 1) (hb : d289776 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d289065, d289776, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
    | true =>
      simp only [d289065, d289776, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d289066 q = 1) (hb : d289777 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d289066, d289777, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
    | true =>
      simp only [d289066, d289777, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d289067 q = 1) (hb : d289778 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d289067, d289778, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d289067, d289778, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro74433 (p : Pattern) (ha : d289087 p = 1) (hb : d290175 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d289059 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d288958 q = 1) (hb : d289773 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d288958, d289773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro74316 q ha hb
    | true =>
      simp only [d288958, d289773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro74317 q ha hb
  have h3 (q : Pattern) (ha : d289060 q = 1) (hb : d289774 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d289060, d289774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d289060, d289774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d289063 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d289064 q = 1) (hb : d289775 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d289064, d289775, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d289064, d289775, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d289085 q = 1) (hb : d289776 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d289085, d289776, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d289085, d289776, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d289086 q = 1) (hb : d289777 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d289086, d289777, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d289086, d289777, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d289087 q = 1) (hb : d290175 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d289087, d290175, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d289087, d290175, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro74434 (p : Pattern) (ha : d289210 p = 1) (hb : d290186 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d289174 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d289179 q = 1) (hb : d290181 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d289179, d290181, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro74356 q ha hb
    | true =>
      simp only [d289179, d290181, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro74362 q ha hb
  have h3 (q : Pattern) (ha : d289180 q = 1) (hb : d290182 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d289180, d290182, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d289180, d290182, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d289206 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d289207 q = 1) (hb : d290183 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d289207, d290183, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d289207, d290183, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d289208 q = 1) (hb : d290184 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d289208, d290184, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d289208, d290184, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d289209 q = 1) (hb : d290185 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d289209, d290185, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d289209, d290185, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d289210 q = 1) (hb : d290186 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d289210, d290186, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d289210, d290186, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro74435 (p : Pattern) (ha : d289223 p = 1) (hb : d290192 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d288966 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d289068 q = 1) (hb : d289779 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d289068, d289779, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro74431 q ha hb
    | true =>
      simp only [d289068, d289779, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro74432 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d289081 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d289082 q = 1) (hb : d289780 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d289082, d289780, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d289082, d289780, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d289083 q = 1) (hb : d290173 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d289083, d290173, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d289083, d290173, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d289084 q = 1) (hb : d290174 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d289084, d290174, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d289084, d290174, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d289088 q = 1) (hb : d290176 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d289088, d290176, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d289088, d290176, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro74433 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d289090 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d289091 q = 1) (hb : d290177 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d289091, d290177, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d289091, d290177, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d289092 q = 1) (hb : d290178 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d289092, d290178, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d289092, d290178, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h11 (q : Pattern) (ha : d289093 q = 1) (hb : d290179 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d289093, d290179, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d289093, d290179, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h12 (q : Pattern) (ha : d289094 q = 1) (hb : d290180 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d289094, d290180, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d289094, d290180, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d289211 q = 1) (hb : d290187 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d289211, d290187, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d289211, d290187, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro74434 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d289218 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d289219 q = 1) (hb : d290188 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d289219, d290188, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d289219, d290188, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d289220 q = 1) (hb : d290189 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d289220, d290189, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d289220, d290189, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h17 (q : Pattern) (ha : d289221 q = 1) (hb : d290190 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d289221, d290190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d289221, d290190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h18 (q : Pattern) (ha : d289222 q = 1) (hb : d290191 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d289222, d290191, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d289222, d290191, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h19 (q : Pattern) (ha : d289223 q = 1) (hb : d290192 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d289223, d290192, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d289223, d290192, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro74436 (p : Pattern) (ha : d289229 p = 1) (hb : d290198 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d289224 q = 1) (hb : d290193 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d289224, d290193, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d289224, d290193, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro74435 q ha hb
  have h2 (q : Pattern) (ha : d289225 q = 1) (hb : d290194 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d289225, d290194, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d289225, d290194, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d289226 q = 1) (hb : d290195 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d289226, d290195, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d289226, d290195, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d289227 q = 1) (hb : d290196 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d289227, d290196, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d289227, d290196, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d289228 q = 1) (hb : d290197 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d289228, d290197, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d289228, d290197, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d289229 q = 1) (hb : d290198 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d289229, d290198, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d289229, d290198, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro74437 (p : Pattern) (ha : d289235 p = 1) (hb : d290204 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d288219 q = 1) (hb : d290115 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d288219, d290115, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro74412 q ha hb
    | true =>
      simp only [d288219, d290115, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro74418 q ha hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d288499 q = 1) (hb : d290142 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d288499, d290142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d288499, d290142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro74424 q ha hb
  have h3 (q : Pattern) (ha : d288500 q = 1) (hb : d290143 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d288500, d290143, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d288500, d290143, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d288845 q = 1) (hb : d290170 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d288845, d290170, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d288845, d290170, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro74430 q ha hb
  have h5 (q : Pattern) (ha : d288846 q = 1) (hb : d290171 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d288846, d290171, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d288846, d290171, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d288847 q = 1) (hb : d290172 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d288847, d290172, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d288847, d290172, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d289230 q = 1) (hb : d290199 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d289230, d290199, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d289230, d290199, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro74436 q ha hb
  have h8 (q : Pattern) (ha : d289231 q = 1) (hb : d290200 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d289231, d290200, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d289231, d290200, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d289232 q = 1) (hb : d290201 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d289232, d290201, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d289232, d290201, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d289233 q = 1) (hb : d290202 q = 1) : d0 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d289233, d290202, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d289233, d290202, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d279903 q = 1) (hb : d280886 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d279903, d280886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d279903, d280886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro71233 q ha hb
  have h12 (q : Pattern) (ha : d279904 q = 1) (hb : d280887 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d279904, d280887, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d279904, d280887, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d279905 q = 1) (hb : d280888 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d279905, d280888, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d279905, d280888, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d279906 q = 1) (hb : d280889 q = 1) : d0 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d279906, d280889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d279906, d280889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d289234 q = 1) (hb : d290203 q = 1) : d0 q = 1 := by
    cases bit : q 10250 with
    | false =>
      simp only [d289234, d290203, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d289234, d290203, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d289235 q = 1) (hb : d290204 q = 1) : d0 q = 1 := by
    cases bit : q 260 with
    | false =>
      simp only [d289235, d290204, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d289235, d290204, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  exact h16 p ha hb
theorem andIntro74438 (p : Pattern) (ha : d289241 p = 1) (hb : d290210 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d289236 q = 1) (hb : d290205 q = 1) : d0 q = 1 := by
    cases bit : q 259 with
    | false =>
      simp only [d289236, d290205, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro74437 q ha hb
    | true =>
      simp only [d289236, d290205, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d289237 q = 1) (hb : d290206 q = 1) : d0 q = 1 := by
    cases bit : q 258 with
    | false =>
      simp only [d289237, d290206, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d289237, d290206, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d289238 q = 1) (hb : d290207 q = 1) : d0 q = 1 := by
    cases bit : q 257 with
    | false =>
      simp only [d289238, d290207, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d289238, d290207, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d289239 q = 1) (hb : d290208 q = 1) : d0 q = 1 := by
    cases bit : q 256 with
    | false =>
      simp only [d289239, d290208, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d289239, d290208, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d289240 q = 1) (hb : d290209 q = 1) : d0 q = 1 := by
    cases bit : q 255 with
    | false =>
      simp only [d289240, d290209, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d289240, d290209, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d289241 q = 1) (hb : d290210 q = 1) : d0 q = 1 := by
    cases bit : q 254 with
    | false =>
      simp only [d289241, d290210, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d289241, d290210, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro74439 (p : Pattern) (ha : d289247 p = 1) (hb : d290216 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d289242 q = 1) (hb : d290211 q = 1) : d0 q = 1 := by
    cases bit : q 253 with
    | false =>
      simp only [d289242, d290211, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro74438 q ha hb
    | true =>
      simp only [d289242, d290211, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d289243 q = 1) (hb : d290212 q = 1) : d0 q = 1 := by
    cases bit : q 252 with
    | false =>
      simp only [d289243, d290212, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d289243, d290212, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d289244 q = 1) (hb : d290213 q = 1) : d0 q = 1 := by
    cases bit : q 251 with
    | false =>
      simp only [d289244, d290213, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d289244, d290213, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d289245 q = 1) (hb : d290214 q = 1) : d0 q = 1 := by
    cases bit : q 250 with
    | false =>
      simp only [d289245, d290214, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d289245, d290214, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d289246 q = 1) (hb : d290215 q = 1) : d0 q = 1 := by
    cases bit : q 249 with
    | false =>
      simp only [d289246, d290215, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d289246, d290215, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d289247 q = 1) (hb : d290216 q = 1) : d0 q = 1 := by
    cases bit : q 245 with
    | false =>
      simp only [d289247, d290216, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d289247, d290216, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro74440 (p : Pattern) (ha : d289253 p = 1) (hb : d290222 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d289248 q = 1) (hb : d290217 q = 1) : d0 q = 1 := by
    cases bit : q 200 with
    | false =>
      simp only [d289248, d290217, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro74439 q ha hb
    | true =>
      simp only [d289248, d290217, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d289249 q = 1) (hb : d290218 q = 1) : d0 q = 1 := by
    cases bit : q 199 with
    | false =>
      simp only [d289249, d290218, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d289249, d290218, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d289250 q = 1) (hb : d290219 q = 1) : d0 q = 1 := by
    cases bit : q 186 with
    | false =>
      simp only [d289250, d290219, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d289250, d290219, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d289251 q = 1) (hb : d290220 q = 1) : d0 q = 1 := by
    cases bit : q 185 with
    | false =>
      simp only [d289251, d290220, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d289251, d290220, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d289252 q = 1) (hb : d290221 q = 1) : d0 q = 1 := by
    cases bit : q 184 with
    | false =>
      simp only [d289252, d290221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d289252, d290221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d289253 q = 1) (hb : d290222 q = 1) : d0 q = 1 := by
    cases bit : q 181 with
    | false =>
      simp only [d289253, d290222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d289253, d290222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro74441 (p : Pattern) (ha : d289259 p = 1) (hb : d290228 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d289254 q = 1) (hb : d290223 q = 1) : d0 q = 1 := by
    cases bit : q 177 with
    | false =>
      simp only [d289254, d290223, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro74440 q ha hb
    | true =>
      simp only [d289254, d290223, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d289255 q = 1) (hb : d290224 q = 1) : d0 q = 1 := by
    cases bit : q 164 with
    | false =>
      simp only [d289255, d290224, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d289255, d290224, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d289256 q = 1) (hb : d290225 q = 1) : d0 q = 1 := by
    cases bit : q 156 with
    | false =>
      simp only [d289256, d290225, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d289256, d290225, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d289257 q = 1) (hb : d290226 q = 1) : d0 q = 1 := by
    cases bit : q 155 with
    | false =>
      simp only [d289257, d290226, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d289257, d290226, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d289258 q = 1) (hb : d290227 q = 1) : d0 q = 1 := by
    cases bit : q 134 with
    | false =>
      simp only [d289258, d290227, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d289258, d290227, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d289259 q = 1) (hb : d290228 q = 1) : d0 q = 1 := by
    cases bit : q 133 with
    | false =>
      simp only [d289259, d290228, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d289259, d290228, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro74442 (p : Pattern) (ha : d289265 p = 1) (hb : d290234 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d289260 q = 1) (hb : d290229 q = 1) : d0 q = 1 := by
    cases bit : q 120 with
    | false =>
      simp only [d289260, d290229, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro74441 q ha hb
    | true =>
      simp only [d289260, d290229, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d289261 q = 1) (hb : d290230 q = 1) : d0 q = 1 := by
    cases bit : q 118 with
    | false =>
      simp only [d289261, d290230, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d289261, d290230, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d289262 q = 1) (hb : d290231 q = 1) : d0 q = 1 := by
    cases bit : q 114 with
    | false =>
      simp only [d289262, d290231, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d289262, d290231, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d289263 q = 1) (hb : d290232 q = 1) : d0 q = 1 := by
    cases bit : q 111 with
    | false =>
      simp only [d289263, d290232, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d289263, d290232, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d289264 q = 1) (hb : d290233 q = 1) : d0 q = 1 := by
    cases bit : q 98 with
    | false =>
      simp only [d289264, d290233, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d289264, d290233, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d289265 q = 1) (hb : d290234 q = 1) : d0 q = 1 := by
    cases bit : q 97 with
    | false =>
      simp only [d289265, d290234, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d289265, d290234, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro74443 (p : Pattern) (ha : d289271 p = 1) (hb : d290240 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d289266 q = 1) (hb : d290235 q = 1) : d0 q = 1 := by
    cases bit : q 94 with
    | false =>
      simp only [d289266, d290235, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro74442 q ha hb
    | true =>
      simp only [d289266, d290235, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d289267 q = 1) (hb : d290236 q = 1) : d0 q = 1 := by
    cases bit : q 76 with
    | false =>
      simp only [d289267, d290236, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d289267, d290236, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d289268 q = 1) (hb : d290237 q = 1) : d0 q = 1 := by
    cases bit : q 67 with
    | false =>
      simp only [d289268, d290237, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d289268, d290237, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d289269 q = 1) (hb : d290238 q = 1) : d0 q = 1 := by
    cases bit : q 52 with
    | false =>
      simp only [d289269, d290238, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d289269, d290238, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d289270 q = 1) (hb : d290239 q = 1) : d0 q = 1 := by
    cases bit : q 47 with
    | false =>
      simp only [d289270, d290239, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d289270, d290239, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d289271 q = 1) (hb : d290240 q = 1) : d0 q = 1 := by
    cases bit : q 46 with
    | false =>
      simp only [d289271, d290240, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d289271, d290240, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro74444 (p : Pattern) (ha : d289277 p = 1) (hb : d290246 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d289272 q = 1) (hb : d290241 q = 1) : d0 q = 1 := by
    cases bit : q 45 with
    | false =>
      simp only [d289272, d290241, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro74443 q ha hb
    | true =>
      simp only [d289272, d290241, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d289273 q = 1) (hb : d290242 q = 1) : d0 q = 1 := by
    cases bit : q 30 with
    | false =>
      simp only [d289273, d290242, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d289273, d290242, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d289274 q = 1) (hb : d290243 q = 1) : d0 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d289274, d290243, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d289274, d290243, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d289275 q = 1) (hb : d290244 q = 1) : d0 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d289275, d290244, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d289275, d290244, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d289276 q = 1) (hb : d290245 q = 1) : d0 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d289276, d290245, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d289276, d290245, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d289277 q = 1) (hb : d290246 q = 1) : d0 q = 1 := by
    cases bit : q 25 with
    | false =>
      simp only [d289277, d290246, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d289277, d290246, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro74445 (p : Pattern) (ha : d104 p = 1) (hb : d289282 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d120 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d126 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d40176 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d43 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d100 q = 1) (hb : d289278 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d100, d289278, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d100, d289278, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d44 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d101 q = 1) (hb : d289279 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d101, d289279, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d101, d289279, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d102 q = 1) (hb : d289280 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d102, d289280, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d102, d289280, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d103 q = 1) (hb : d289281 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d103, d289281, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d103, d289281, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d104 q = 1) (hb : d289282 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d104, d289282, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d104, d289282, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro74446 (p : Pattern) (ha : d111 p = 1) (hb : d289287 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d120 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d126 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d40176 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d43 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d100 q = 1) (hb : d289278 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d100, d289278, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d100, d289278, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d44 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d101 q = 1) (hb : d289279 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d101, d289279, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d101, d289279, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d102 q = 1) (hb : d289280 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d102, d289280, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d102, d289280, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d103 q = 1) (hb : d289281 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d103, d289281, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d103, d289281, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d198 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d202 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d40183 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d50 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d107 q = 1) (hb : d289283 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d107, d289283, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d107, d289283, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d51 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d108 q = 1) (hb : d289284 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d108, d289284, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d108, d289284, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d109 q = 1) (hb : d289285 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d109, d289285, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d109, d289285, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d110 q = 1) (hb : d289286 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d110, d289286, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d110, d289286, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d111 q = 1) (hb : d289287 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d111, d289287, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d111, d289287, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro74447 (p : Pattern) (ha : d406 p = 1) (hb : d289294 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d40183 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d50 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d107 q = 1) (hb : d289283 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d107, d289283, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d107, d289283, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d51 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d108 q = 1) (hb : d289284 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d108, d289284, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d108, d289284, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d109 q = 1) (hb : d289292 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d109, d289292, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d109, d289292, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d110 q = 1) (hb : d289293 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d110, d289293, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d110, d289293, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d406 q = 1) (hb : d289294 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d406, d289294, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d406, d289294, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro74448 (p : Pattern) (ha : d462 p = 1) (hb : d289304 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d40219 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d84 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d458 q = 1) (hb : d289300 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d458, d289300, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d458, d289300, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d85 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d459 q = 1) (hb : d289301 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d459, d289301, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d459, d289301, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d460 q = 1) (hb : d289302 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d460, d289302, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d460, d289302, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d461 q = 1) (hb : d289303 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d461, d289303, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d461, d289303, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d462 q = 1) (hb : d289304 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d462, d289304, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d462, d289304, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro74449 (p : Pattern) (ha : d53647 p = 1) (hb : d289310 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d114 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d112 q = 1) (hb : d289288 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d112, d289288, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro74445 q ha hb
    | true =>
      simp only [d112, d289288, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro74446 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d214 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d113 q = 1) (hb : d289289 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d113, d289289, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d113, d289289, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d53637 q = 1) (hb : d289290 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d53637, d289290, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d53637, d289290, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d53638 q = 1) (hb : d289291 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d53638, d289291, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53638, d289291, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d407 q = 1) (hb : d289295 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d407, d289295, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d407, d289295, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro74447 q ha hb
  have h8 (q : Pattern) (ha : d53639 q = 1) (hb : d289296 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d53639, d289296, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d53639, d289296, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h9 (q : Pattern) (ha : d53640 q = 1) (hb : d289297 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d53640, d289297, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d53640, d289297, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h10 (q : Pattern) (ha : d53641 q = 1) (hb : d289298 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d53641, d289298, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d53641, d289298, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h11 (q : Pattern) (ha : d53642 q = 1) (hb : d289299 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d53642, d289299, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d53642, d289299, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d463 q = 1) (hb : d289305 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d463, d289305, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d463, d289305, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro74448 q ha hb
  have h13 (q : Pattern) (ha : d53643 q = 1) (hb : d289306 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d53643, d289306, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d53643, d289306, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h14 (q : Pattern) (ha : d53644 q = 1) (hb : d289307 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d53644, d289307, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d53644, d289307, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h15 (q : Pattern) (ha : d53645 q = 1) (hb : d289308 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d53645, d289308, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d53645, d289308, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h16 (q : Pattern) (ha : d53646 q = 1) (hb : d289309 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d53646, d289309, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d53646, d289309, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h17 (q : Pattern) (ha : d53647 q = 1) (hb : d289310 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d53647, d289310, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d53647, d289310, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  exact h17 p ha hb
theorem andIntro74450 (p : Pattern) (ha : d40240 p = 1) (hb : d289320 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d40256 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d40262 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d40297 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d40176 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d40236 q = 1) (hb : d289316 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d40236, d289316, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d40236, d289316, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d40332 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d40237 q = 1) (hb : d289317 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d40237, d289317, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d40237, d289317, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d40238 q = 1) (hb : d289318 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d40238, d289318, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d40238, d289318, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d40239 q = 1) (hb : d289319 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d40239, d289319, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d40239, d289319, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d40240 q = 1) (hb : d289320 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d40240, d289320, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d40240, d289320, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro74451 (p : Pattern) (ha : d40247 p = 1) (hb : d289325 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d40256 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d40262 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d40297 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d40176 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d40236 q = 1) (hb : d289316 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d40236, d289316, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d40236, d289316, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d40332 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d40237 q = 1) (hb : d289317 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d40237, d289317, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d40237, d289317, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d40238 q = 1) (hb : d289318 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d40238, d289318, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d40238, d289318, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d40239 q = 1) (hb : d289319 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d40239, d289319, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d40239, d289319, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d40341 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d40345 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d40347 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d40183 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d40243 q = 1) (hb : d289321 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d40243, d289321, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d40243, d289321, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d40353 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d40244 q = 1) (hb : d289322 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d40244, d289322, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d40244, d289322, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d40245 q = 1) (hb : d289323 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d40245, d289323, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d40245, d289323, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d40246 q = 1) (hb : d289324 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d40246, d289324, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d40246, d289324, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d40247 q = 1) (hb : d289325 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d40247, d289325, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d40247, d289325, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro74452 (p : Pattern) (ha : d289332 p = 1) (hb : d290066 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d40347 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d40183 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d40243 q = 1) (hb : d289321 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d40243, d289321, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d40243, d289321, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d40353 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d40244 q = 1) (hb : d289322 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d40244, d289322, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d40244, d289322, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d40245 q = 1) (hb : d289330 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d40245, d289330, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d40245, d289330, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d40246 q = 1) (hb : d289331 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d40246, d289331, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d40246, d289331, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d289332 q = 1) (hb : d290066 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d289332, d290066, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d289332, d290066, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
  exact h8 p ha hb
theorem andIntro74453 (p : Pattern) (ha : d289342 p = 1) (hb : d290076 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d40395 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d40219 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d289338 q = 1) (hb : d290072 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d289338, d290072, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d289338, d290072, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d40421 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d289339 q = 1) (hb : d290073 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d289339, d290073, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d289339, d290073, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d289340 q = 1) (hb : d290074 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d289340, d290074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d289340, d290074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d289341 q = 1) (hb : d290075 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d289341, d290075, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d289341, d290075, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d289342 q = 1) (hb : d290076 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d289342, d290076, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d289342, d290076, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro74454 (p : Pattern) (ha : d289348 p = 1) (hb : d290082 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d40250 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d40248 q = 1) (hb : d289326 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d40248, d289326, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro74450 q ha hb
    | true =>
      simp only [d40248, d289326, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro74451 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d40360 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d40249 q = 1) (hb : d289327 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d40249, d289327, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d40249, d289327, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d289328 q = 1) (hb : d290064 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d289328, d290064, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d289328, d290064, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d289329 q = 1) (hb : d290065 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d289329, d290065, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d289329, d290065, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d289333 q = 1) (hb : d290067 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d289333, d290067, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d289333, d290067, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro74452 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d407 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d289334 q = 1) (hb : d290068 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d289334, d290068, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d289334, d290068, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d289335 q = 1) (hb : d290069 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d289335, d290069, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d289335, d290069, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h11 (q : Pattern) (ha : d289336 q = 1) (hb : d290070 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d289336, d290070, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d289336, d290070, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h12 (q : Pattern) (ha : d289337 q = 1) (hb : d290071 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d289337, d290071, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d289337, d290071, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d289343 q = 1) (hb : d290077 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d289343, d290077, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d289343, d290077, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro74453 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d463 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d289344 q = 1) (hb : d290078 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d289344, d290078, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d289344, d290078, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d289345 q = 1) (hb : d290079 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d289345, d290079, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d289345, d290079, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h17 (q : Pattern) (ha : d289346 q = 1) (hb : d290080 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d289346, d290080, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d289346, d290080, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h18 (q : Pattern) (ha : d289347 q = 1) (hb : d290081 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d289347, d290081, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d289347, d290081, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h19 (q : Pattern) (ha : d289348 q = 1) (hb : d290082 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d289348, d290082, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d289348, d290082, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro74455 (p : Pattern) (ha : d289354 p = 1) (hb : d290088 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d99 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d53648 q = 1) (hb : d289311 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d53648, d289311, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d53648, d289311, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro74449 q ha hb
  have h3 (q : Pattern) (ha : d53649 q = 1) (hb : d289312 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d53649, d289312, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d53649, d289312, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d53650 q = 1) (hb : d289313 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d53650, d289313, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d53650, d289313, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d53651 q = 1) (hb : d289314 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d53651, d289314, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d53651, d289314, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d53652 q = 1) (hb : d289315 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d53652, d289315, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53652, d289315, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d289349 q = 1) (hb : d290083 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d289349, d290083, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d289349, d290083, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro74454 q ha hb
  have h8 (q : Pattern) (ha : d289350 q = 1) (hb : d290084 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d289350, d290084, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d289350, d290084, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d289351 q = 1) (hb : d290085 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d289351, d290085, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d289351, d290085, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d289352 q = 1) (hb : d290086 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d289352, d290086, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d289352, d290086, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d289353 q = 1) (hb : d290087 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d289353, d290087, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d289353, d290087, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d289354 q = 1) (hb : d290088 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d289354, d290088, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
    | true =>
      simp only [d289354, d290088, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  exact h12 p ha hb
theorem andIntro74456 (p : Pattern) (ha : d40460 p = 1) (hb : d289359 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d40481 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d40490 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d40539 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d40455 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d40456 q = 1) (hb : d289355 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d40456, d289355, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d40456, d289355, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d40590 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d40457 q = 1) (hb : d289356 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d40457, d289356, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d40457, d289356, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d40458 q = 1) (hb : d289357 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d40458, d289357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d40458, d289357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d40459 q = 1) (hb : d289358 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d40459, d289358, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d40459, d289358, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d40460 q = 1) (hb : d289359 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d40460, d289359, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d40460, d289359, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro74457 (p : Pattern) (ha : d40470 p = 1) (hb : d289364 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d40481 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d40490 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d40539 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d40455 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d40456 q = 1) (hb : d289355 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d40456, d289355, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d40456, d289355, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d40590 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d40457 q = 1) (hb : d289356 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d40457, d289356, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d40457, d289356, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d40458 q = 1) (hb : d289357 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d40458, d289357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d40458, d289357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d40459 q = 1) (hb : d289358 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d40459, d289358, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d40459, d289358, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d40600 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d40605 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d40607 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d40465 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d40466 q = 1) (hb : d289360 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d40466, d289360, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d40466, d289360, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d40614 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d40467 q = 1) (hb : d289361 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d40467, d289361, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d40467, d289361, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d40468 q = 1) (hb : d289362 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d40468, d289362, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d40468, d289362, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d40469 q = 1) (hb : d289363 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d40469, d289363, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d40469, d289363, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d40470 q = 1) (hb : d289364 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d40470, d289364, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d40470, d289364, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro74458 (p : Pattern) (ha : d289371 p = 1) (hb : d290091 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d40607 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d40465 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d40466 q = 1) (hb : d289360 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d40466, d289360, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d40466, d289360, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d40614 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d40467 q = 1) (hb : d289361 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d40467, d289361, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d40467, d289361, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d40468 q = 1) (hb : d289369 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d40468, d289369, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d40468, d289369, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d40469 q = 1) (hb : d289370 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d40469, d289370, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d40469, d289370, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d289371 q = 1) (hb : d290091 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d289371, d290091, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d289371, d290091, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
  exact h8 p ha hb
theorem andIntro74459 (p : Pattern) (ha : d289381 p = 1) (hb : d290102 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d40690 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d290097 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d289377 q = 1) (hb : d290098 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d289377, d290098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d289377, d290098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d40730 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d289378 q = 1) (hb : d290099 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d289378, d290099, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d289378, d290099, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d289379 q = 1) (hb : d290100 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d289379, d290100, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d289379, d290100, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d289380 q = 1) (hb : d290101 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d289380, d290101, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d289380, d290101, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d289381 q = 1) (hb : d290102 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d289381, d290102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d289381, d290102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro74460 (p : Pattern) (ha : d289387 p = 1) (hb : d290108 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d40473 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d40471 q = 1) (hb : d289365 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d40471, d289365, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro74456 q ha hb
    | true =>
      simp only [d40471, d289365, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro74457 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d40632 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d40472 q = 1) (hb : d289366 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d40472, d289366, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d40472, d289366, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d289367 q = 1) (hb : d290089 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d289367, d290089, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d289367, d290089, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d289368 q = 1) (hb : d290090 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d289368, d290090, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d289368, d290090, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d289372 q = 1) (hb : d290092 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d289372, d290092, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d289372, d290092, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro74458 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d40641 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d289373 q = 1) (hb : d290093 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d289373, d290093, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d289373, d290093, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d289374 q = 1) (hb : d290094 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d289374, d290094, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d289374, d290094, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h11 (q : Pattern) (ha : d289375 q = 1) (hb : d290095 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d289375, d290095, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d289375, d290095, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h12 (q : Pattern) (ha : d289376 q = 1) (hb : d290096 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d289376, d290096, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d289376, d290096, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d289382 q = 1) (hb : d290103 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d289382, d290103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d289382, d290103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro74459 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d40746 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d289383 q = 1) (hb : d290104 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d289383, d290104, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d289383, d290104, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d289384 q = 1) (hb : d290105 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d289384, d290105, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d289384, d290105, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h17 (q : Pattern) (ha : d289385 q = 1) (hb : d290106 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d289385, d290106, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d289385, d290106, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h18 (q : Pattern) (ha : d289386 q = 1) (hb : d290107 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d289386, d290107, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d289386, d290107, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h19 (q : Pattern) (ha : d289387 q = 1) (hb : d290108 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d289387, d290108, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d289387, d290108, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro74461 (p : Pattern) (ha : d289393 p = 1) (hb : d290114 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d289388 q = 1) (hb : d290109 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d289388, d290109, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d289388, d290109, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro74460 q ha hb
  have h2 (q : Pattern) (ha : d289389 q = 1) (hb : d290110 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d289389, d290110, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d289389, d290110, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d289390 q = 1) (hb : d290111 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d289390, d290111, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d289390, d290111, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d289391 q = 1) (hb : d290112 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d289391, d290112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d289391, d290112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d289392 q = 1) (hb : d290113 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d289392, d290113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d289392, d290113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d289393 q = 1) (hb : d290114 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d289393, d290114, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d289393, d290114, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro74462 (p : Pattern) (ha : d40799 p = 1) (hb : d289399 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d40820 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d40829 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d40881 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d40794 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d40795 q = 1) (hb : d289395 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d40795, d289395, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d40795, d289395, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d40954 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d40796 q = 1) (hb : d289396 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d40796, d289396, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d40796, d289396, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d40797 q = 1) (hb : d289397 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d40797, d289397, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d40797, d289397, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d40798 q = 1) (hb : d289398 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d40798, d289398, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d40798, d289398, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d40799 q = 1) (hb : d289399 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d40799, d289399, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d40799, d289399, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro74463 (p : Pattern) (ha : d40809 p = 1) (hb : d289404 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d40820 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d40829 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d40881 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d40794 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d40795 q = 1) (hb : d289395 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d40795, d289395, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d40795, d289395, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d40954 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d40796 q = 1) (hb : d289396 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d40796, d289396, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d40796, d289396, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d40797 q = 1) (hb : d289397 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d40797, d289397, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d40797, d289397, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d40798 q = 1) (hb : d289398 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d40798, d289398, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d40798, d289398, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d40964 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d40969 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d40971 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d40804 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d40805 q = 1) (hb : d289400 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d40805, d289400, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d40805, d289400, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d40978 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d40806 q = 1) (hb : d289401 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d40806, d289401, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d40806, d289401, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d40807 q = 1) (hb : d289402 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d40807, d289402, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d40807, d289402, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d40808 q = 1) (hb : d289403 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d40808, d289403, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d40808, d289403, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d40809 q = 1) (hb : d289404 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d40809, d289404, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d40809, d289404, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro74464 (p : Pattern) (ha : d289411 p = 1) (hb : d290118 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d40971 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d40804 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d40805 q = 1) (hb : d289400 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d40805, d289400, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d40805, d289400, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d40978 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d40806 q = 1) (hb : d289401 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d40806, d289401, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d40806, d289401, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d40807 q = 1) (hb : d289409 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d40807, d289409, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d40807, d289409, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d40808 q = 1) (hb : d289410 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d40808, d289410, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d40808, d289410, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d289411 q = 1) (hb : d290118 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d289411, d290118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d289411, d290118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
  exact h8 p ha hb
theorem andIntro74465 (p : Pattern) (ha : d289421 p = 1) (hb : d290129 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d41071 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d290124 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d289417 q = 1) (hb : d290125 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d289417, d290125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d289417, d290125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d41126 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d289418 q = 1) (hb : d290126 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d289418, d290126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d289418, d290126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d289419 q = 1) (hb : d290127 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d289419, d290127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d289419, d290127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d289420 q = 1) (hb : d290128 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d289420, d290128, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d289420, d290128, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d289421 q = 1) (hb : d290129 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d289421, d290129, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d289421, d290129, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro74466 (p : Pattern) (ha : d289427 p = 1) (hb : d290135 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d40812 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d40810 q = 1) (hb : d289405 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d40810, d289405, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro74462 q ha hb
    | true =>
      simp only [d40810, d289405, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro74463 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d40996 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d40811 q = 1) (hb : d289406 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d40811, d289406, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d40811, d289406, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d289407 q = 1) (hb : d290116 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d289407, d290116, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d289407, d290116, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d289408 q = 1) (hb : d290117 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d289408, d290117, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d289408, d290117, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d289412 q = 1) (hb : d290119 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d289412, d290119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d289412, d290119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro74464 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d41005 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d289413 q = 1) (hb : d290120 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d289413, d290120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d289413, d290120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d289414 q = 1) (hb : d290121 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d289414, d290121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d289414, d290121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h11 (q : Pattern) (ha : d289415 q = 1) (hb : d290122 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d289415, d290122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d289415, d290122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h12 (q : Pattern) (ha : d289416 q = 1) (hb : d290123 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d289416, d290123, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d289416, d290123, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d289422 q = 1) (hb : d290130 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d289422, d290130, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d289422, d290130, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro74465 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d41142 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d289423 q = 1) (hb : d290131 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d289423, d290131, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d289423, d290131, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d289424 q = 1) (hb : d290132 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d289424, d290132, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d289424, d290132, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h17 (q : Pattern) (ha : d289425 q = 1) (hb : d290133 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d289425, d290133, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d289425, d290133, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h18 (q : Pattern) (ha : d289426 q = 1) (hb : d290134 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d289426, d290134, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d289426, d290134, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h19 (q : Pattern) (ha : d289427 q = 1) (hb : d290135 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d289427, d290135, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d289427, d290135, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro74467 (p : Pattern) (ha : d289433 p = 1) (hb : d290141 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d289428 q = 1) (hb : d290136 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d289428, d290136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d289428, d290136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro74466 q ha hb
  have h2 (q : Pattern) (ha : d289429 q = 1) (hb : d290137 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d289429, d290137, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d289429, d290137, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d289430 q = 1) (hb : d290138 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d289430, d290138, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d289430, d290138, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d289431 q = 1) (hb : d290139 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d289431, d290139, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d289431, d290139, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d289432 q = 1) (hb : d290140 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d289432, d290140, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d289432, d290140, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d289433 q = 1) (hb : d290141 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d289433, d290141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d289433, d290141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro74468 (p : Pattern) (ha : d289484 p = 1) (hb : d290251 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d41255 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d41264 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d41307 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d289479 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d289480 q = 1) (hb : d290247 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d289480, d290247, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d289480, d290247, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d41417 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d289481 q = 1) (hb : d290248 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d289481, d290248, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d289481, d290248, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d289482 q = 1) (hb : d290249 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d289482, d290249, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d289482, d290249, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d289483 q = 1) (hb : d290250 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d289483, d290250, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d289483, d290250, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d289484 q = 1) (hb : d290251 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d289484, d290251, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d289484, d290251, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro74469 (p : Pattern) (ha : d289494 p = 1) (hb : d290256 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d41255 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d41264 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d41307 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d289479 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d289480 q = 1) (hb : d290247 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d289480, d290247, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d289480, d290247, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d41417 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d289481 q = 1) (hb : d290248 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d289481, d290248, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d289481, d290248, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d289482 q = 1) (hb : d290249 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d289482, d290249, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d289482, d290249, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d289483 q = 1) (hb : d290250 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d289483, d290250, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d289483, d290250, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d41427 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d41432 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d41434 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d289489 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d289490 q = 1) (hb : d290252 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d289490, d290252, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d289490, d290252, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d41441 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d289491 q = 1) (hb : d290253 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d289491, d290253, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d289491, d290253, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d289492 q = 1) (hb : d290254 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d289492, d290254, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d289492, d290254, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d289493 q = 1) (hb : d290255 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d289493, d290255, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d289493, d290255, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d289494 q = 1) (hb : d290256 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d289494, d290256, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d289494, d290256, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro74470 (p : Pattern) (ha : d290146 p = 1) (hb : d290263 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d41434 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d289489 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d289490 q = 1) (hb : d290252 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d289490, d290252, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d289490, d290252, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d41441 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d289491 q = 1) (hb : d290253 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d289491, d290253, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d289491, d290253, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d289492 q = 1) (hb : d290261 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d289492, d290261, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d289492, d290261, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d289493 q = 1) (hb : d290262 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d289493, d290262, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d289493, d290262, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d290146 q = 1) (hb : d290263 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d290146, d290263, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d290146, d290263, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro74471 (p : Pattern) (ha : d290157 p = 1) (hb : d290273 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d41552 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d290152 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d290153 q = 1) (hb : d290269 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d290153, d290269, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d290153, d290269, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d41625 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d290154 q = 1) (hb : d290270 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d290154, d290270, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d290154, d290270, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d290155 q = 1) (hb : d290271 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d290155, d290271, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d290155, d290271, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d290156 q = 1) (hb : d290272 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d290156, d290272, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d290156, d290272, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d290157 q = 1) (hb : d290273 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d290157, d290273, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d290157, d290273, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro74472 (p : Pattern) (ha : d290163 p = 1) (hb : d290279 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d41247 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d289495 q = 1) (hb : d290257 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d289495, d290257, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro74468 q ha hb
    | true =>
      simp only [d289495, d290257, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro74469 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d41459 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d289496 q = 1) (hb : d290258 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d289496, d290258, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d289496, d290258, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d290144 q = 1) (hb : d290259 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d290144, d290259, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d290144, d290259, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d290145 q = 1) (hb : d290260 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d290145, d290260, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d290145, d290260, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d290147 q = 1) (hb : d290264 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d290147, d290264, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d290147, d290264, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro74470 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d41468 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d290148 q = 1) (hb : d290265 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d290148, d290265, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d290148, d290265, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d290149 q = 1) (hb : d290266 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d290149, d290266, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d290149, d290266, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h11 (q : Pattern) (ha : d290150 q = 1) (hb : d290267 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d290150, d290267, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d290150, d290267, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h12 (q : Pattern) (ha : d290151 q = 1) (hb : d290268 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d290151, d290268, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d290151, d290268, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d290158 q = 1) (hb : d290274 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d290158, d290274, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d290158, d290274, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro74471 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d41641 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d290159 q = 1) (hb : d290275 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d290159, d290275, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d290159, d290275, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d290160 q = 1) (hb : d290276 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d290160, d290276, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d290160, d290276, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h17 (q : Pattern) (ha : d290161 q = 1) (hb : d290277 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d290161, d290277, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d290161, d290277, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h18 (q : Pattern) (ha : d290162 q = 1) (hb : d290278 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d290162, d290278, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d290162, d290278, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h19 (q : Pattern) (ha : d290163 q = 1) (hb : d290279 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d290163, d290279, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d290163, d290279, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro74473 (p : Pattern) (ha : d290169 p = 1) (hb : d290285 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d290164 q = 1) (hb : d290280 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d290164, d290280, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d290164, d290280, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro74472 q ha hb
  have h2 (q : Pattern) (ha : d290165 q = 1) (hb : d290281 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d290165, d290281, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d290165, d290281, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d290166 q = 1) (hb : d290282 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d290166, d290282, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d290166, d290282, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d290167 q = 1) (hb : d290283 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d290167, d290283, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d290167, d290283, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d290168 q = 1) (hb : d290284 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d290168, d290284, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d290168, d290284, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d290169 q = 1) (hb : d290285 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d290169, d290285, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d290169, d290285, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro74474 (p : Pattern) (ha : d289768 p = 1) (hb : d290293 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d41782 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d41791 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d41821 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d289763 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d289764 q = 1) (hb : d290289 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d289764, d290289, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d289764, d290289, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d41951 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d289765 q = 1) (hb : d290290 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d289765, d290290, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d289765, d290290, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d289766 q = 1) (hb : d290291 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d289766, d290291, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d289766, d290291, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d289767 q = 1) (hb : d290292 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d289767, d290292, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d289767, d290292, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d289768 q = 1) (hb : d290293 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d289768, d290293, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d289768, d290293, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro74475 (p : Pattern) (ha : d289778 p = 1) (hb : d290298 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d41782 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d41791 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d41821 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d289763 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d289764 q = 1) (hb : d290289 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d289764, d290289, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d289764, d290289, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d41951 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d289765 q = 1) (hb : d290290 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d289765, d290290, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d289765, d290290, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d289766 q = 1) (hb : d290291 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d289766, d290291, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d289766, d290291, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d289767 q = 1) (hb : d290292 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d289767, d290292, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d289767, d290292, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d41961 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d41966 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d41968 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d289773 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d289774 q = 1) (hb : d290294 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d289774, d290294, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d289774, d290294, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d41975 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d289775 q = 1) (hb : d290295 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d289775, d290295, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d289775, d290295, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d289776 q = 1) (hb : d290296 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d289776, d290296, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d289776, d290296, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d289777 q = 1) (hb : d290297 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d289777, d290297, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d289777, d290297, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d289778 q = 1) (hb : d290298 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d289778, d290298, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d289778, d290298, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro74476 (p : Pattern) (ha : d290175 p = 1) (hb : d290305 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d41968 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d289773 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d289774 q = 1) (hb : d290294 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d289774, d290294, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d289774, d290294, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d41975 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d289775 q = 1) (hb : d290295 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d289775, d290295, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d289775, d290295, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d289776 q = 1) (hb : d290303 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d289776, d290303, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d289776, d290303, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d289777 q = 1) (hb : d290304 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d289777, d290304, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d289777, d290304, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d290175 q = 1) (hb : d290305 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d290175, d290305, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d290175, d290305, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro74477 (p : Pattern) (ha : d290186 p = 1) (hb : d290315 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d42086 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d290181 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d290182 q = 1) (hb : d290311 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d290182, d290311, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d290182, d290311, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d42170 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d290183 q = 1) (hb : d290312 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d290183, d290312, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d290183, d290312, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d290184 q = 1) (hb : d290313 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d290184, d290313, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d290184, d290313, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d290185 q = 1) (hb : d290314 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d290185, d290314, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d290185, d290314, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d290186 q = 1) (hb : d290315 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d290186, d290315, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d290186, d290315, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro74478 (p : Pattern) (ha : d290192 p = 1) (hb : d290321 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d41774 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d289779 q = 1) (hb : d290299 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d289779, d290299, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro74474 q ha hb
    | true =>
      simp only [d289779, d290299, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro74475 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d41993 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d289780 q = 1) (hb : d290300 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d289780, d290300, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d289780, d290300, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d290173 q = 1) (hb : d290301 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d290173, d290301, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d290173, d290301, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d290174 q = 1) (hb : d290302 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d290174, d290302, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d290174, d290302, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d290176 q = 1) (hb : d290306 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d290176, d290306, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d290176, d290306, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro74476 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d42002 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d290177 q = 1) (hb : d290307 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d290177, d290307, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d290177, d290307, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d290178 q = 1) (hb : d290308 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d290178, d290308, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d290178, d290308, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h11 (q : Pattern) (ha : d290179 q = 1) (hb : d290309 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d290179, d290309, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d290179, d290309, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h12 (q : Pattern) (ha : d290180 q = 1) (hb : d290310 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d290180, d290310, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d290180, d290310, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d290187 q = 1) (hb : d290316 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d290187, d290316, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d290187, d290316, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro74477 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d42186 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d290188 q = 1) (hb : d290317 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d290188, d290317, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d290188, d290317, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d290189 q = 1) (hb : d290318 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d290189, d290318, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d290189, d290318, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h17 (q : Pattern) (ha : d290190 q = 1) (hb : d290319 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d290190, d290319, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d290190, d290319, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h18 (q : Pattern) (ha : d290191 q = 1) (hb : d290320 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d290191, d290320, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d290191, d290320, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h19 (q : Pattern) (ha : d290192 q = 1) (hb : d290321 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d290192, d290321, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d290192, d290321, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro74479 (p : Pattern) (ha : d290198 p = 1) (hb : d290327 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d290193 q = 1) (hb : d290322 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d290193, d290322, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d290193, d290322, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro74478 q ha hb
  have h2 (q : Pattern) (ha : d290194 q = 1) (hb : d290323 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d290194, d290323, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d290194, d290323, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d290195 q = 1) (hb : d290324 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d290195, d290324, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d290195, d290324, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d290196 q = 1) (hb : d290325 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d290196, d290325, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d290196, d290325, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d290197 q = 1) (hb : d290326 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d290197, d290326, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d290197, d290326, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d290198 q = 1) (hb : d290327 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d290198, d290327, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d290198, d290327, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro74480 (p : Pattern) (ha : d290204 p = 1) (hb : d290333 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d289394 q = 1) (hb : d290115 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d289394, d290115, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro74455 q ha hb
    | true =>
      simp only [d289394, d290115, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro74461 q ha hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d289434 q = 1) (hb : d290142 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d289434, d290142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d289434, d290142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro74467 q ha hb
  have h3 (q : Pattern) (ha : d289435 q = 1) (hb : d290143 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d289435, d290143, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d289435, d290143, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d290170 q = 1) (hb : d290286 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d290170, d290286, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d290170, d290286, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro74473 q ha hb
  have h5 (q : Pattern) (ha : d290171 q = 1) (hb : d290287 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d290171, d290287, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d290171, d290287, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d290172 q = 1) (hb : d290288 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d290172, d290288, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d290172, d290288, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d290199 q = 1) (hb : d290328 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d290199, d290328, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d290199, d290328, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro74479 q ha hb
  have h8 (q : Pattern) (ha : d290200 q = 1) (hb : d290329 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d290200, d290329, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d290200, d290329, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d290201 q = 1) (hb : d290330 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d290201, d290330, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d290201, d290330, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d290202 q = 1) (hb : d290331 q = 1) : d0 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d290202, d290331, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d290202, d290331, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d279903 q = 1) (hb : d281058 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d279903, d281058, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d279903, d281058, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro71271 q ha hb
  have h12 (q : Pattern) (ha : d279904 q = 1) (hb : d281059 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d279904, d281059, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d279904, d281059, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d279905 q = 1) (hb : d281060 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d279905, d281060, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d279905, d281060, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d279906 q = 1) (hb : d281061 q = 1) : d0 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d279906, d281061, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d279906, d281061, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d290203 q = 1) (hb : d290332 q = 1) : d0 q = 1 := by
    cases bit : q 10250 with
    | false =>
      simp only [d290203, d290332, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d290203, d290332, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d290204 q = 1) (hb : d290333 q = 1) : d0 q = 1 := by
    cases bit : q 260 with
    | false =>
      simp only [d290204, d290333, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d290204, d290333, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  exact h16 p ha hb
theorem andIntro74481 (p : Pattern) (ha : d290210 p = 1) (hb : d290339 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d290205 q = 1) (hb : d290334 q = 1) : d0 q = 1 := by
    cases bit : q 259 with
    | false =>
      simp only [d290205, d290334, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro74480 q ha hb
    | true =>
      simp only [d290205, d290334, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d290206 q = 1) (hb : d290335 q = 1) : d0 q = 1 := by
    cases bit : q 258 with
    | false =>
      simp only [d290206, d290335, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d290206, d290335, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d290207 q = 1) (hb : d290336 q = 1) : d0 q = 1 := by
    cases bit : q 257 with
    | false =>
      simp only [d290207, d290336, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d290207, d290336, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d290208 q = 1) (hb : d290337 q = 1) : d0 q = 1 := by
    cases bit : q 256 with
    | false =>
      simp only [d290208, d290337, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d290208, d290337, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d290209 q = 1) (hb : d290338 q = 1) : d0 q = 1 := by
    cases bit : q 255 with
    | false =>
      simp only [d290209, d290338, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d290209, d290338, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d290210 q = 1) (hb : d290339 q = 1) : d0 q = 1 := by
    cases bit : q 254 with
    | false =>
      simp only [d290210, d290339, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d290210, d290339, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro74482 (p : Pattern) (ha : d290216 p = 1) (hb : d290345 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d290211 q = 1) (hb : d290340 q = 1) : d0 q = 1 := by
    cases bit : q 253 with
    | false =>
      simp only [d290211, d290340, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro74481 q ha hb
    | true =>
      simp only [d290211, d290340, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d290212 q = 1) (hb : d290341 q = 1) : d0 q = 1 := by
    cases bit : q 252 with
    | false =>
      simp only [d290212, d290341, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d290212, d290341, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d290213 q = 1) (hb : d290342 q = 1) : d0 q = 1 := by
    cases bit : q 251 with
    | false =>
      simp only [d290213, d290342, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d290213, d290342, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d290214 q = 1) (hb : d290343 q = 1) : d0 q = 1 := by
    cases bit : q 250 with
    | false =>
      simp only [d290214, d290343, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d290214, d290343, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d290215 q = 1) (hb : d290344 q = 1) : d0 q = 1 := by
    cases bit : q 249 with
    | false =>
      simp only [d290215, d290344, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d290215, d290344, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d290216 q = 1) (hb : d290345 q = 1) : d0 q = 1 := by
    cases bit : q 245 with
    | false =>
      simp only [d290216, d290345, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d290216, d290345, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro74483 (p : Pattern) (ha : d290222 p = 1) (hb : d290351 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d290217 q = 1) (hb : d290346 q = 1) : d0 q = 1 := by
    cases bit : q 200 with
    | false =>
      simp only [d290217, d290346, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro74482 q ha hb
    | true =>
      simp only [d290217, d290346, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d290218 q = 1) (hb : d290347 q = 1) : d0 q = 1 := by
    cases bit : q 199 with
    | false =>
      simp only [d290218, d290347, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d290218, d290347, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d290219 q = 1) (hb : d290348 q = 1) : d0 q = 1 := by
    cases bit : q 186 with
    | false =>
      simp only [d290219, d290348, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d290219, d290348, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d290220 q = 1) (hb : d290349 q = 1) : d0 q = 1 := by
    cases bit : q 185 with
    | false =>
      simp only [d290220, d290349, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d290220, d290349, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d290221 q = 1) (hb : d290350 q = 1) : d0 q = 1 := by
    cases bit : q 184 with
    | false =>
      simp only [d290221, d290350, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d290221, d290350, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d290222 q = 1) (hb : d290351 q = 1) : d0 q = 1 := by
    cases bit : q 181 with
    | false =>
      simp only [d290222, d290351, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d290222, d290351, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro74484 (p : Pattern) (ha : d290228 p = 1) (hb : d290357 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d290223 q = 1) (hb : d290352 q = 1) : d0 q = 1 := by
    cases bit : q 177 with
    | false =>
      simp only [d290223, d290352, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro74483 q ha hb
    | true =>
      simp only [d290223, d290352, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d290224 q = 1) (hb : d290353 q = 1) : d0 q = 1 := by
    cases bit : q 164 with
    | false =>
      simp only [d290224, d290353, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d290224, d290353, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d290225 q = 1) (hb : d290354 q = 1) : d0 q = 1 := by
    cases bit : q 156 with
    | false =>
      simp only [d290225, d290354, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d290225, d290354, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d290226 q = 1) (hb : d290355 q = 1) : d0 q = 1 := by
    cases bit : q 155 with
    | false =>
      simp only [d290226, d290355, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d290226, d290355, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d290227 q = 1) (hb : d290356 q = 1) : d0 q = 1 := by
    cases bit : q 134 with
    | false =>
      simp only [d290227, d290356, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d290227, d290356, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d290228 q = 1) (hb : d290357 q = 1) : d0 q = 1 := by
    cases bit : q 133 with
    | false =>
      simp only [d290228, d290357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d290228, d290357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro74485 (p : Pattern) (ha : d290234 p = 1) (hb : d290363 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d290229 q = 1) (hb : d290358 q = 1) : d0 q = 1 := by
    cases bit : q 120 with
    | false =>
      simp only [d290229, d290358, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro74484 q ha hb
    | true =>
      simp only [d290229, d290358, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d290230 q = 1) (hb : d290359 q = 1) : d0 q = 1 := by
    cases bit : q 118 with
    | false =>
      simp only [d290230, d290359, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d290230, d290359, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d290231 q = 1) (hb : d290360 q = 1) : d0 q = 1 := by
    cases bit : q 114 with
    | false =>
      simp only [d290231, d290360, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d290231, d290360, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d290232 q = 1) (hb : d290361 q = 1) : d0 q = 1 := by
    cases bit : q 111 with
    | false =>
      simp only [d290232, d290361, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d290232, d290361, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d290233 q = 1) (hb : d290362 q = 1) : d0 q = 1 := by
    cases bit : q 98 with
    | false =>
      simp only [d290233, d290362, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d290233, d290362, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d290234 q = 1) (hb : d290363 q = 1) : d0 q = 1 := by
    cases bit : q 97 with
    | false =>
      simp only [d290234, d290363, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d290234, d290363, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro74486 (p : Pattern) (ha : d290240 p = 1) (hb : d290369 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d290235 q = 1) (hb : d290364 q = 1) : d0 q = 1 := by
    cases bit : q 94 with
    | false =>
      simp only [d290235, d290364, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro74485 q ha hb
    | true =>
      simp only [d290235, d290364, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d290236 q = 1) (hb : d290365 q = 1) : d0 q = 1 := by
    cases bit : q 76 with
    | false =>
      simp only [d290236, d290365, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d290236, d290365, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d290237 q = 1) (hb : d290366 q = 1) : d0 q = 1 := by
    cases bit : q 67 with
    | false =>
      simp only [d290237, d290366, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d290237, d290366, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d290238 q = 1) (hb : d290367 q = 1) : d0 q = 1 := by
    cases bit : q 52 with
    | false =>
      simp only [d290238, d290367, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d290238, d290367, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d290239 q = 1) (hb : d290368 q = 1) : d0 q = 1 := by
    cases bit : q 47 with
    | false =>
      simp only [d290239, d290368, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d290239, d290368, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d290240 q = 1) (hb : d290369 q = 1) : d0 q = 1 := by
    cases bit : q 46 with
    | false =>
      simp only [d290240, d290369, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d290240, d290369, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro74487 (p : Pattern) (ha : d290246 p = 1) (hb : d290375 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d290241 q = 1) (hb : d290370 q = 1) : d0 q = 1 := by
    cases bit : q 45 with
    | false =>
      simp only [d290241, d290370, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro74486 q ha hb
    | true =>
      simp only [d290241, d290370, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d290242 q = 1) (hb : d290371 q = 1) : d0 q = 1 := by
    cases bit : q 30 with
    | false =>
      simp only [d290242, d290371, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d290242, d290371, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d290243 q = 1) (hb : d290372 q = 1) : d0 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d290243, d290372, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d290243, d290372, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d290244 q = 1) (hb : d290373 q = 1) : d0 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d290244, d290373, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d290244, d290373, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d290245 q = 1) (hb : d290374 q = 1) : d0 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d290245, d290374, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d290245, d290374, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d290246 q = 1) (hb : d290375 q = 1) : d0 q = 1 := by
    cases bit : q 25 with
    | false =>
      simp only [d290246, d290375, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d290246, d290375, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro74488 (p : Pattern) (ha : d30638 p = 1) (hb : d251389 p = 1) : d251392 p = 1 := by
  have h0 (q : Pattern) (ha : d25434 q = 1) (hb : d202304 q = 1) : d25434 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d20 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d30635 q = 1) (hb : d251389 q = 1) : d25435 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d30635, d251389, d25435, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d30635, d251389, d25435, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d21 q = 1) (hb : d251389 q = 1) : d21 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d30636 q = 1) (hb : d251389 q = 1) : d251390 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d30636, d251390, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d30636, d251390, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d251389 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d30637 q = 1) (hb : d251389 q = 1) : d251391 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d30637, d251391, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d30637, d251391, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d23 q = 1) (hb : d251389 q = 1) : d23 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d30638 q = 1) (hb : d251389 q = 1) : d251392 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d30638, d251392, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d30638, d251392, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro74489 (p : Pattern) (ha : d30644 p = 1) (hb : d251389 p = 1) : d251398 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d251389 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d30639 q = 1) (hb : d251389 q = 1) : d251393 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d30639, d251393, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro74488 q ha hb
    | true =>
      simp only [d30639, d251393, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d30640 q = 1) (hb : d251389 q = 1) : d251394 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d30640, d251394, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d30640, d251394, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d30641 q = 1) (hb : d251389 q = 1) : d251395 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d30641, d251395, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d30641, d251395, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d30642 q = 1) (hb : d251389 q = 1) : d251396 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d30642, d251396, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d30642, d251396, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d28 q = 1) (hb : d251389 q = 1) : d28 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d30643 q = 1) (hb : d251389 q = 1) : d251397 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d30643, d251397, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d30643, d251397, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d29 q = 1) (hb : d251389 q = 1) : d29 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d30644 q = 1) (hb : d251389 q = 1) : d251398 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d30644, d251398, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d30644, d251398, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro74490 (p : Pattern) (ha : d30650 p = 1) (hb : d251389 p = 1) : d251404 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d251389 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d30 q = 1) (hb : d251389 q = 1) : d30 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d30645 q = 1) (hb : d251389 q = 1) : d251399 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d30645, d251399, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro74489 q ha hb
    | true =>
      simp only [d30645, d251399, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d30646 q = 1) (hb : d251389 q = 1) : d251400 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d30646, d251400, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d30646, d251400, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d30647 q = 1) (hb : d251389 q = 1) : d251401 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d30647, d251401, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d30647, d251401, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d33 q = 1) (hb : d251389 q = 1) : d33 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d30648 q = 1) (hb : d251389 q = 1) : d251402 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d30648, d251402, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d30648, d251402, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d34 q = 1) (hb : d251389 q = 1) : d34 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d30649 q = 1) (hb : d251389 q = 1) : d251403 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d30649, d251403, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d30649, d251403, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d30650 q = 1) (hb : d251389 q = 1) : d251404 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d30650, d251404, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d30650, d251404, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h9 p ha hb
theorem andIntro74491 (p : Pattern) (ha : d30656 p = 1) (hb : d251389 p = 1) : d251410 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d251389 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d30651 q = 1) (hb : d251389 q = 1) : d251405 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d30651, d251405, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro74490 q ha hb
    | true =>
      simp only [d30651, d251405, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d30652 q = 1) (hb : d251389 q = 1) : d251406 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d30652, d251406, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d30652, d251406, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d38 q = 1) (hb : d251389 q = 1) : d38 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d30653 q = 1) (hb : d251389 q = 1) : d251407 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d30653, d251407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d30653, d251407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d30654 q = 1) (hb : d251389 q = 1) : d251408 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d30654, d251408, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d30654, d251408, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d30655 q = 1) (hb : d251389 q = 1) : d251409 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d30655, d251409, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d30655, d251409, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d30656 q = 1) (hb : d251389 q = 1) : d251410 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d30656, d251410, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d30656, d251410, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro74492 (p : Pattern) (ha : d245354 p = 1) (hb : d251389 p = 1) : d251416 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d251389 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d120 q = 1) (hb : d251389 q = 1) : d120 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d126 q = 1) (hb : d251389 q = 1) : d126 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d42 q = 1) (hb : d251389 q = 1) : d42 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d30657 q = 1) (hb : d251389 q = 1) : d251411 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d30657, d251411, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro74491 q ha hb
    | true =>
      simp only [d30657, d251411, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d245350 q = 1) (hb : d251389 q = 1) : d251412 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d245350, d251412, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d245350, d251412, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d44 q = 1) (hb : d251389 q = 1) : d44 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d245351 q = 1) (hb : d251389 q = 1) : d251413 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d245351, d251413, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d245351, d251413, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d245352 q = 1) (hb : d251389 q = 1) : d251414 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d245352, d251414, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d245352, d251414, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d245353 q = 1) (hb : d251389 q = 1) : d251415 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d245353, d251415, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d245353, d251415, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d245354 q = 1) (hb : d251389 q = 1) : d251416 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d245354, d251416, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d245354, d251416, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro74493 (p : Pattern) (ha : d30663 p = 1) (hb : d251389 p = 1) : d251417 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d251389 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d30651 q = 1) (hb : d251389 q = 1) : d251405 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d30651, d251405, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro74490 q ha hb
    | true =>
      simp only [d30651, d251405, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d30652 q = 1) (hb : d251389 q = 1) : d251406 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d30652, d251406, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d30652, d251406, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d38 q = 1) (hb : d251389 q = 1) : d38 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d30653 q = 1) (hb : d251389 q = 1) : d251407 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d30653, d251407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d30653, d251407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d30654 q = 1) (hb : d251389 q = 1) : d251408 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d30654, d251408, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d30654, d251408, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d30655 q = 1) (hb : d251389 q = 1) : d251409 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d30655, d251409, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d30655, d251409, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d30663 q = 1) (hb : d251389 q = 1) : d251417 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d30663, d251417, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d30663, d251417, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h7 p ha hb
theorem andIntro74494 (p : Pattern) (ha : d245359 p = 1) (hb : d251389 p = 1) : d251423 p = 1 := by
  have h0 (q : Pattern) (ha : d120 q = 1) (hb : d251389 q = 1) : d120 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d126 q = 1) (hb : d251389 q = 1) : d126 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d42 q = 1) (hb : d251389 q = 1) : d42 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d30657 q = 1) (hb : d251389 q = 1) : d251411 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d30657, d251411, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro74491 q ha hb
    | true =>
      simp only [d30657, d251411, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d251389 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d245350 q = 1) (hb : d251389 q = 1) : d251412 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d245350, d251412, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d245350, d251412, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d44 q = 1) (hb : d251389 q = 1) : d44 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d245351 q = 1) (hb : d251389 q = 1) : d251413 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d245351, d251413, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d245351, d251413, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d245352 q = 1) (hb : d251389 q = 1) : d251414 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d245352, d251414, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d245352, d251414, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d245353 q = 1) (hb : d251389 q = 1) : d251415 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d245353, d251415, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d245353, d251415, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d198 q = 1) (hb : d251389 q = 1) : d198 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d202 q = 1) (hb : d251389 q = 1) : d202 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d49 q = 1) (hb : d251389 q = 1) : d49 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d30664 q = 1) (hb : d251389 q = 1) : d251418 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d30664, d251418, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro74493 q ha hb
    | true =>
      simp only [d30664, d251418, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d245355 q = 1) (hb : d251389 q = 1) : d251419 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d245355, d251419, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d245355, d251419, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h15 (q : Pattern) (ha : d51 q = 1) (hb : d251389 q = 1) : d51 q = 1 := by
    exact ha
  have h16 (q : Pattern) (ha : d245356 q = 1) (hb : d251389 q = 1) : d251420 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d245356, d251420, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d245356, d251420, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d245357 q = 1) (hb : d251389 q = 1) : d251421 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d245357, d251421, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d245357, d251421, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d245358 q = 1) (hb : d251389 q = 1) : d251422 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d245358, d251422, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d245358, d251422, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d245359 q = 1) (hb : d251389 q = 1) : d251423 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d245359, d251423, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d245359, d251423, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro74495 (p : Pattern) (ha : d245366 p = 1) (hb : d251389 p = 1) : d251430 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d251389 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d49 q = 1) (hb : d251389 q = 1) : d49 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d30664 q = 1) (hb : d251389 q = 1) : d251418 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d30664, d251418, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro74493 q ha hb
    | true =>
      simp only [d30664, d251418, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d245355 q = 1) (hb : d251389 q = 1) : d251419 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d245355, d251419, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d245355, d251419, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d51 q = 1) (hb : d251389 q = 1) : d51 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d245356 q = 1) (hb : d251389 q = 1) : d251420 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d245356, d251420, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d245356, d251420, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d245364 q = 1) (hb : d251389 q = 1) : d251428 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d245364, d251428, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d245364, d251428, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d245365 q = 1) (hb : d251389 q = 1) : d251429 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d245365, d251429, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d245365, d251429, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d245366 q = 1) (hb : d251389 q = 1) : d251430 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d245366, d251430, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d245366, d251430, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro74496 (p : Pattern) (ha : d30687 p = 1) (hb : d251389 p = 1) : d251441 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d251389 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d30682 q = 1) (hb : d251389 q = 1) : d251436 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d30682, d251436, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d30682, d251436, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro74488 q ha hb
  have h2 (q : Pattern) (ha : d30639 q = 1) (hb : d251389 q = 1) : d251393 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d30639, d251393, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro74488 q ha hb
    | true =>
      simp only [d30639, d251393, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d30683 q = 1) (hb : d251389 q = 1) : d251437 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d30683, d251437, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d30683, d251437, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d30640 q = 1) (hb : d251389 q = 1) : d251394 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d30640, d251394, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d30640, d251394, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d30684 q = 1) (hb : d251389 q = 1) : d251438 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d30684, d251438, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d30684, d251438, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d30685 q = 1) (hb : d251389 q = 1) : d251439 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d30685, d251439, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d30685, d251439, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d69 q = 1) (hb : d251389 q = 1) : d69 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d30686 q = 1) (hb : d251389 q = 1) : d251440 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d30686, d251440, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d30686, d251440, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d70 q = 1) (hb : d251389 q = 1) : d70 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d30687 q = 1) (hb : d251389 q = 1) : d251441 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d30687, d251441, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d30687, d251441, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro74497 (p : Pattern) (ha : d30693 p = 1) (hb : d251389 p = 1) : d251447 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d251389 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d71 q = 1) (hb : d251389 q = 1) : d71 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d30688 q = 1) (hb : d251389 q = 1) : d251442 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d30688, d251442, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro74496 q ha hb
    | true =>
      simp only [d30688, d251442, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d30689 q = 1) (hb : d251389 q = 1) : d251443 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d30689, d251443, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d30689, d251443, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d30690 q = 1) (hb : d251389 q = 1) : d251444 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d30690, d251444, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d30690, d251444, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d74 q = 1) (hb : d251389 q = 1) : d74 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d30691 q = 1) (hb : d251389 q = 1) : d251445 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d30691, d251445, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d30691, d251445, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d75 q = 1) (hb : d251389 q = 1) : d75 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d30692 q = 1) (hb : d251389 q = 1) : d251446 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d30692, d251446, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d30692, d251446, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d30693 q = 1) (hb : d251389 q = 1) : d251447 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d30693, d251447, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d30693, d251447, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h9 p ha hb
theorem andIntro74498 (p : Pattern) (ha : d30699 p = 1) (hb : d251389 p = 1) : d251453 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d251389 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d30694 q = 1) (hb : d251389 q = 1) : d251448 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d30694, d251448, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro74497 q ha hb
    | true =>
      simp only [d30694, d251448, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d30695 q = 1) (hb : d251389 q = 1) : d251449 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d30695, d251449, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d30695, d251449, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d79 q = 1) (hb : d251389 q = 1) : d79 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d30696 q = 1) (hb : d251389 q = 1) : d251450 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d30696, d251450, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d30696, d251450, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d30697 q = 1) (hb : d251389 q = 1) : d251451 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d30697, d251451, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d30697, d251451, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d30698 q = 1) (hb : d251389 q = 1) : d251452 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d30698, d251452, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d30698, d251452, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d30699 q = 1) (hb : d251389 q = 1) : d251453 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d30699, d251453, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d30699, d251453, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h7 p ha hb
theorem andIntro74499 (p : Pattern) (ha : d245376 p = 1) (hb : d251389 p = 1) : d251459 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d251389 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d83 q = 1) (hb : d251389 q = 1) : d83 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d30700 q = 1) (hb : d251389 q = 1) : d251454 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d30700, d251454, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro74498 q ha hb
    | true =>
      simp only [d30700, d251454, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d245372 q = 1) (hb : d251389 q = 1) : d251455 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d245372, d251455, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d245372, d251455, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d85 q = 1) (hb : d251389 q = 1) : d85 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d245373 q = 1) (hb : d251389 q = 1) : d251456 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d245373, d251456, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d245373, d251456, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d245374 q = 1) (hb : d251389 q = 1) : d251457 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d245374, d251457, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d245374, d251457, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d245375 q = 1) (hb : d251389 q = 1) : d251458 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d245375, d251458, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d245375, d251458, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d245376 q = 1) (hb : d251389 q = 1) : d251459 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d245376, d251459, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d245376, d251459, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
end NetHack.Soko22Hazard87
